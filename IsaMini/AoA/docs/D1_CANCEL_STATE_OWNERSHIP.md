# D1 — `_cancel` destroys a `Minilang_State` that a parked sub-agent still holds

> **Status:** root cause fully traced (static, evidence-backed). **Not reproduced.** **Not fixed.**
> **Audience:** a fresh Claude Code session picking this up from zero.
> **Line numbers drift** — every claim below is anchored on a *symbol name*. Grep for it.

---

## 0. TL;DR

`Minilang_State` objects are **shared between adjacent nodes** of the proof tree:
a node's "resulting state" **is literally its next sibling's `ml_state` object**.
`Node._cancel` calls `reset()` on that shared object, and `reset()` sends an RPC that
**deletes the state from Isabelle's server-side state table**.

A **parked worker (sub-agent)** holds `role.target.ml_state` across the whole refresh
cycle. When a refresh cascade cancels the worker's predecessor, that state is destroyed
under the worker's feet. On re-prime, the worker queries the dead state →
ML `beginning_state_not_found` → uncaught `IsabelleError` → `call_tool` does
`sys.exit(1)` → **the whole host process dies**.

The codebase **already** protects one consumer against exactly this
(`Session.resolve_context_at`, with the explicit doctrine *"no silent substitution"*).
It never applied the same protection to the worker path.

---

## 1. Concepts (don't conflate)

| Concept | What it is | Cardinality |
|---|---|---|
| Isabelle / REPL session | one Isabelle process behind the `Connection` (default `127.0.0.1:6666`) | 1 per `by aoa` |
| **`Minilang_State`** | a **named snapshot in Isabelle's server-side state table** (`$init`, `$1`, …). Python holds only the name. | many (per node, before/after) |
| Python `Session` | an agent context (planner / worker / interaction fork) | many |

A `Node`'s `ml_state` is the **state BEFORE executing that node**
(see the comment inside `Session._prefetch_worker_premises`:
*Node's "state before executing the node"*).

---

## 2. The aliasing — the source of everything

`NonLeaf_Node._resulting_state_of_child`:

```python
def _resulting_state_of_child(self, node):
    for i, child in enumerate(self.sub_nodes):
        if child is node:
            if i < len(self.sub_nodes) - 1:
                return self.sub_nodes[i+1].ml_state          # ← the NEXT sibling's object
            else:
                return self._resulting_state_of_all_children()
```

and `StdBlock._resulting_state_of_all_children` → `return self._state_before_ending_`.

`Node.resulting_state()` = `self.parent._resulting_state_of_child(self)`.

So, inside one block with children `c0..c[n-1]`:

```
c0.ml_state = clone(_state_after_beginning())     # created at fill time
c[i].resulting_state()  IS  c[i+1].ml_state       # i < n-1   ← SAME OBJECT
c[n-1].resulting_state() IS  self._state_before_ending_
```

**No ownership. No refcount.**

---

## 3. `reset()` is a destructive, server-side delete

`Minilang_State.reset`:

```python
async def reset(self) -> None:
    """Remove this state from the Isabelle state table and mark as uninitialized."""
    await self.connection.callback("IsaMini.reset_state", self.name)
    self._initialized = False
    ...
```

Note: the node's `ml_state` **pointer is immutable** (comment at `Node.__init__`:
*the pointer of self.ml_state is immutable*). `reset()` does not swap the object — it
**empties it**: the server-side entry is gone, `initialized()` becomes False.
*"The shell survives; the contents are deleted."*

---

## 4. What `_cancel` is FOR (it is not wrong in itself)

`CANCELLED` means **"this step was never executed, because an earlier step failed"**
(rendered as `Error: cancelled (step 2 failed)`; `pending` in quickview). Distinct from
`FAILURE` ("this step itself errored").

```python
# Node._cancel
if self.status.status is CANCELLED: return          # idempotent
self._cancelled_by = cancelled_by                   # (1) who is to blame
self.status = EVALUATION_CACNCELLED                 # (2) mark
await self.resulting_state().reset()                # (3) release the now-meaningless state

# StdBlock._cancel additionally
await self._state_before_ending_.reset()
for child in self.sub_nodes:
    await child._cancel(cancelled_by)               # (4) RECURSES over the whole subtree
```

`NonLeaf_Node._failed_predecessor_id` walks back through `_cancelled_by` to name the
真 culprit.

The `reset()` in (3) has **two legitimate reasons**:

1. **Correctness** — the predecessor never ran, so the successor's before-state does not
   logically exist. Leaving it `initialized()==True` means it still holds a **stale state
   from a previous, now-invalid evaluation**; anyone using it is using the wrong state.
2. **Resource** — the state lives in Isabelle's server-side table; not deleting it leaks.

**So reset-on-cancel is right, from the tree's own point of view.** The defect is *who
owns the object it deletes*.

### Call sites of `_cancel` (two families)

**A. Cascade** — "the chain broke, everything downstream is void":
- `NonLeaf_Node._refresh_all_children_after` — every sibling after the first failing one
- `StdBlock._refresh_me_alone`'s child loop — same, inside a block
- the `GoalContainer` analogue
- `StdBlock._cancel`'s **own recursion** into `sub_nodes`

**B. A newly attached node lands in an already-broken region** (no refresh, straight to
cancel) — inside `fill` / `insert_before` / `amend` paths, each passing
`parent._failed_predecessor_id(node)`.

### Exact arithmetic (who dies)

In the cascade, if `c[j]` is the **first** failing child:

| node | cancelled? | its `ml_state` destroyed? |
|---|---|---|
| `c[j]` (the failure) | no — status is FAILURE | — |
| `c[j+1]` | **yes** | **no** (its predecessor `c[j]` was not cancelled) |
| `c[j+2] … c[n-1]` | yes | **yes** |
| block's `_state_before_ending_` | — | **yes** (killed by `c[n-1]._cancel`) |

And **`StdBlock._cancel` on any ancestor** wipes, recursively, every descendant's
before-state **except each block's first child**, plus every `_state_before_ending_`.

> **Rule:** `X.ml_state` is destroyed **iff `X`'s immediate predecessor sibling is `_cancel`ed.**
> Corollary (worth verifying): a worker parked on the **first child** of its parent is
> mechanically spared by this path — which would explain why the bug is **intermittent**.

---

## 5. The victim: a parked worker

`Role_Worker.target` is the anchor. `Session._prefetch_worker_premises`:

```python
target = self.role.target
names = [n.ascii for n in target._ctxt_before_me().hyps]
pairs = await target.ml_state.fact_propositions(names)     # ← NO initialized() guard
```

It holds `target.ml_state` **across the entire refresh cycle**.

### Where it actually blows up

Not at "resume" as a distinct action. The two call sites of `_prefetch_worker_premises`
(both in `mcp_http_server.py`) are:

- `_request_tool_logic` — the worker **BLOCKS inside `request`** while the planner proves
  helper lemmas into the GlobalEnv; when control returns, the premise cache is re-primed.
  The comment there states the broken assumption verbatim:
  > *"New facts may now sit in scope BEFORE this worker's target (auto-proved general
  > Haves) … — the premise cache assumed that set immutable."*
- `_run_struggle_checkpoint`

---

## 6. The amplifier

`ProofMCPHTTPServer.call_tool`:

```python
except Exception as e:
    session.log_tool_response(..., f"UNEXPECTED ERROR: {type(e).__name__}: {e}")
    sys.exit(1)
```

This is **deliberate** ("so latent bugs surface early").
**The user has explicitly decided NOT to change this.** Consequence: **any** consumer you
forget to guard still kills the process. Completeness of the guard is mandatory.

---

## 7. The trigger chain

`Root.sub_nodes == [GlobalEnv, goal_1, goal_2, …]` and **`GlobalEnv._body_affects_siblings = True`**
(default on `StdBlock` is `False`). So in `StdBlock._refresh_me_alone`:

```python
if can_continue and self._body_affects_siblings:
    await self.parent._refresh_all_children_after(self, can_continue)
```

⇒ **any GlobalEnv body change re-evaluates every top-level goal.**
Semantically correct: a new global lemma changes the Isabelle context, so all downstream
states are stale and must be re-derived.

The chain (this is `184d718`'s own comment, recovered from git history):

```
Bug: `request`/request_lemmas auto-proves a general lemma into the GlobalEnv;
`Root._refresh_all_children_after` then re-evaluates EVERY top-level goal,
including the subtree where the requesting worker is PARKED mid-proof.
That re-eval cancels nodes in the parked subtree, and this `reset()` removes
(server-side) the `Minilang_State` the worker still holds as `target.ml_state`.
On resume, `_prefetch_worker_premises` queries that dead state
-> ML `beginning_state_not_found` -> uncaught IsabelleError
-> `call_tool` does `sys.exit(1)`, killing the host.
```

The irony: the worker asked for a lemma **so it could see it**; granting the request
demolishes the ground it was standing on.

---

## 8. Three stacked defects

| | defect | location |
|---|---|---|
| **D1** | **ownership/aliasing** — `_cancel` destroys a resource it does not exclusively own (the successor's before-state); no refcount, no liveness check | `Node._cancel`, `StdBlock._cancel` |
| **D2** | **missing guard** — the worker re-prime path queries the state without `initialized()` | `Session._prefetch_worker_premises` |
| **D3** | **fatal handler** — a recoverable `IsabelleError` is escalated to `sys.exit(1)` | `call_tool` |

---

## 9. History

```
184d718  2026-06-28  Qiyuan Xu
  AoA: temporarily skip Minilang_State reset on node cancel (avoid host crash)
```

It simply **commented out both `reset()` calls**, and stated the restore precondition:

> *"Restore this once the cascade no longer touches parked subtrees (**and/or** prefetch
> guards on `initialized()`)."*

It also admitted the price:

> *"Skipping the reset keeps the (**possibly stale/wrong**) state alive so the worker
> survives instead of the whole process dying."*

**That workaround trades a loud crash for silent use of a wrong proof state — strictly
worse in a theorem prover.**

**On 2026-07-09 the user directed the restore.** Both `reset()` calls are now ACTIVE in
the working tree, and the `TODO(revert)` comment blocks were deleted.
**Neither precondition is satisfied:**
- `_prefetch_worker_premises` still has no `initialized()` guard;
- grepping `parked` shows **no** parked-subtree special-case anywhere in the cascade.

**⇒ The landmine is armed again.** Empirically it did not detonate in the test suite —
see §11 for why that proves nothing.

---

## 10. The two findings that should shape the fix

### 10.1 The doctrine already exists — it was just not applied to workers

`Session.resolve_context_at` (grep the string `cancelled or failed region`) carries this
docstring:

> *"…(`Node._cancel` reset the relevant `Minilang_State`) or was never initialized (a
> block whose beginning op failed). Such a state has no live server-side name, so feeding
> it to retrieval would surface an opaque `beginning_state_not_found` from ML. **We detect
> it with `.initialized()` and raise a clear ValueError instead — no silent substitution.**"*

and implements exactly `if not st.initialized(): raise ValueError(dead_region_msg)`.

**The author already knew all of this.** The `retrieval`/`query` consumer is guarded.
The **worker** consumer is not. This is an inconsistency, not an unknown.

### 10.2 Worker protection is enforced at the `edit` boundary — and the cascade bypasses it

The codebase already has a coherent worker-protection discipline:

- `Session._edit_verdict` → an `edit` touching a region that holds a live sub-agent is **LOCKED**
- `amend` **tears down** the target's worker (`_amend_preserves_worker` decides; tests
  `AmendKeepsWorker` / `AmendTearsDownWorker` / `AmendRevertKeepsWorker`)
- `_dispatch_blocked_by` keeps live handles an **antichain**

> **All of it hangs off the `edit` API boundary. The refresh cascade goes around that
> boundary: it can cancel a worker's whole region — and destroy its states — without ever
> producing a verdict or a teardown.**

That is the root cause **at the right altitude**, and it matches the user's own intuition:
*"the sub-agent design never considered cancel/pending."*

### 10.3 The invariant that makes the fix simple

`c[i+1].ml_state` is (re)initialized precisely when `c[i]` executes successfully
(`_execute_opr(self.ml_state, op, self.resulting_state())` writes **into** the successor's
before-state). Therefore:

> **`target.ml_state.initialized()` ⟺ the chain leading to `target` is live.**

which is *the same predicate* `resolve_context_at` uses. Consequences:

| situation | outcome |
|---|---|
| after the GlobalEnv re-refresh the worker's region is **still live** | the predecessor re-executes ⇒ `target.ml_state` is **automatically re-created** ⇒ prefetch works ⇒ **nothing to fix** |
| the re-refresh makes an **earlier** step newly fail (or an earlier top-level goal fails) ⇒ the region is cancelled | `target.ml_state` is destroyed and **there is nothing to rebuild it from** — its predecessor no longer evaluates |

**So the crash only exists on the unhappy path, and on that path the worker's sub-goal
logically no longer exists** (its context depends on a step that no longer evaluates).
"Re-thread the worker's target" is **impossible** there — there is no thread to lay.

**⇒ Not resuming (or deferring the resume) is the only correct semantics on that path.**

---

## 11. Why the test suite is silent (and why that is not reassurance)

- `config.DISABLE_REQUEST_GENERAL_LEMMAS = True` (default, added by `a10a958`) empties
  `general_lemmas` inside `_request_tool_logic`, so the auto-prove-into-GlobalEnv path
  **never runs** — in tests *or in production*.
- The tests that would exercise the path (`RequestLemmasAutoProve`, `RefuteOrSurrender`,
  `RequestFinishesTarget`) therefore assert a **no-op**; their goldens were re-blessed on
  2026-07-09 to record the gated behaviour.
- `RequestLemmasInEnvTarget` — the regression test for general-lemma **placement** inside
  the GlobalEnv — was **deleted** on 2026-07-09 (it crashed on `index(None)` under the gate).

> **There is currently ZERO regression coverage of the crash path.**

Residual risk, stated honestly:
- **Mitigated:** the specific `request_lemmas` trigger named in `184d718` cannot fire while
  the gate is on.
- **NOT mitigated:** the underlying trigger is *any* GlobalEnv mutation while a worker is
  parked (`GlobalEnv._body_affects_siblings = True`). A planner `edit` into `global.N`
  plausibly does the same. **This is inferred, not demonstrated.**

---

## 12. Why the obvious fixes are wrong

- ❌ **"make the cascade skip parked subtrees"** — semantically wrong. The whole point of
  `request_lemmas` is to put a lemma into the GlobalEnv so the worker can *see* it. The
  worker's target state was derived from the **old** context; skipping the re-derivation
  means the worker never sees the lemma.
- ⚠️ **"just add an `initialized()` guard to prefetch"** — stops the crash (D2/D3), but the
  worker then proceeds with an empty premise cache over a dead region. **Haemostasis, not
  a cure.** (Still: it is the doctrine `resolve_context_at` already follows, and it must be
  part of any fix.)
- ❌ **"keep 184d718's skip"** — trades a crash for silent wrong-state proofs.
- ✅ **Consumer-side liveness gate + explicit dispatcher notification**, reusing the
  existing `.initialized()` doctrine, with a decision about the worker's fate.

---

## 13. Proposed direction (to be confirmed)

1. **Extract** the `.initialized()` dead-region check out of `Session.resolve_context_at`
   into a shared helper (repo rule: *Always Reuse Code — Never Reinvent the Wheel*).
   Something like `Session.usable_state_at(node) -> Minilang_State` / `node.in_dead_region()`.
2. **Gate the worker** on it, before `_prefetch_worker_premises` touches ML — at **both**
   call sites (`_request_tool_logic`, `_run_struggle_checkpoint`).
3. **Honour "no silent substitution"**: on a dead region, do **not** resume; surface it to
   the dispatcher explicitly.
4. Consider the **producer side** too: make the cascade obey the same discipline the `edit`
   boundary already enforces (i.e. when `_cancel` is about to swallow a node whose subtree
   holds a live `worker_handle`, either tear the worker down as `amend` does, or mark it
   invalidated). Purely consumer-side is enough to stop the crash; the producer side is what
   stops a worker being parked forever on a permanently dead region.

---

## 14. Open design questions (**must be answered by the user before implementing**)

**Q1 — On a dead region, what happens to the worker?**
(a) stay parked + notify the planner (*"your edit invalidated this sub-agent's region; fix
step X, or drop it with `cancel_subagent`"*); (b) tear it down (mirroring `amend`'s
existing teardown, losing its partial proof); (c) auto-resume once the region becomes live.

**Q2 — Which predicate gates the worker?**
`target.ml_state.initialized()` (state-level; identical to `resolve_context_at`; the exact
precondition of the crash) **vs** `target`-or-ancestor `status == CANCELLED` (status-level).
§10.3 argues they coincide, **but this is not proven** — e.g. a block whose *beginning op*
failed was never initialized at all, without any cancel. **Verify before choosing.**

**Q3 — After the region comes back live, is it still the same goal?**
The context gained a global lemma, so `target`'s goal statement may differ. Is the worker's
partial proof still valid? Should resume perform a **goal-identity check** and re-dispatch
on mismatch?

**Q4 — Are there other consumers? (BLOCKING — do this first, read-only)**
Because `sys.exit(1)` stays, **any** unguarded consumer of a possibly-dead state still kills
the host. **Enumerate every ML-touching use of a worker-reachable `ml_state` /
`_state_before_ending_`** (`fact_propositions`, `check_term`, `execute`, `clone`,
`leading_goal`, rendering paths, `WorkerHandle.run_until_yield`, …) and classify each as
guarded / unguarded. Only then implement.

---

## 15. Reproduction plan (nothing here has been reproduced yet)

The mechanism is proven statically; the **concrete production trace is not**. Build a repro
before touching `_cancel`.

1. In a dedicated `@model_test`, **temporarily** flip the gate off inside the test only
   (save/restore, exactly as the existing tests already save/restore `mcp._run_worker_on`):
   ```python
   _saved = mcp.config.DISABLE_REQUEST_GENERAL_LEMMAS
   mcp.config.DISABLE_REQUEST_GENERAL_LEMMAS = False
   try: ...
   finally: mcp.config.DISABLE_REQUEST_GENERAL_LEMMAS = _saved
   ```
   (The production default must stay `True`.)
2. Build a top-level goal with **two failing `Obvious` steps**, park a worker on the
   **later** one (so, per §4's arithmetic, `target.ml_state` is destroyed by its
   predecessor's `_cancel`).
3. Have the worker call `request` with a general lemma → planner auto-proves it into the
   GlobalEnv → `GlobalEnv._body_affects_siblings` → `Root._refresh_all_children_after` →
   cascade → `_cancel` → `reset()`.
4. Expect: `_prefetch_worker_premises` → `beginning_state_not_found` → (were `sys.exit(1)`
   not there) `IsabelleError`. **Warning: if it reproduces, the REPL/host on 6666 dies and
   must be restarted by the user.**
5. Also test the §4 corollary: a worker parked on the **first child** of its parent should
   *not* see its `ml_state` destroyed. If confirmed, that explains the intermittency.

---

## 16. Constraints for whoever works on this

- **Shared working tree**, other agents run concurrently. **Never** `git stash` /
  `checkout` / `reset --hard` / `clean`. Commit on `main`, never branch. Before committing,
  ALWAYS inspect `git diff --cached` — the shared index has, in the past, silently carried
  another agent's staged files into a commit.
- **`contrib/Isa-Mini` is a git submodule** (`git@github.com:xqyww123/Isa-Mini.git`, branch `main`).
- **Never modify a golden YAML (`Tests/*.yml`) without explicit user approval** — no
  exceptions, even when the new output is obviously right.
- **Never run two `test_AoA.py` concurrently** (shared REPL on 6666). ⚠️ A naive
  `while pgrep -f test_AoA.py; do sleep …; done` **deadlocks**: the waiting shell's own
  command line contains the string `test_AoA.py`, so it matches itself forever. Filter by
  process `comm` (`ps -o comm=`) being `python*`.
- Always redirect `test_AoA.py` output (it is huge). `python -u`.
- `remote_error` from a model test **always** means a golden diff; the real diff is at
  `Tests/<name>.diff` / `<name>.actual.yml`.
- **Do NOT change the `sys.exit(1)` fatal handler** — the user decided this explicitly.
- Editing `.ML` requires the user to restart the REPL. Editing `.py` does not.

---

## 17. State of the working tree as of 2026-07-09 (uncommitted unless noted)

Relevant to this bug:
- `model.py` — **both `reset()` calls RESTORED** in `Node._cancel` / `StdBlock._cancel`;
  the `TODO(revert)` comment blocks were removed. **This is what re-arms D1.**
- `test.py` — `RequestLemmasInEnvTarget` deleted; `SubagentHintScopeOneShot` deepened
  (3 → 6 nested `Have`s) to keep clearing `_SUBAGENT_HINT_DEPTH = 5`.
- `Tests/` — `RequestLemmasInEnvTarget.{thy,yml}` deleted; 6 goldens re-blessed
  (`Derive6`, `Derive7`, `SubagentHintScopeOneShot`, `RequestLemmasAutoProve`,
  `RefuteOrSurrender`, `RequestFinishesTarget`); ~46 `Test_*.thy` gained
  `imports Complex_Main` (because `Agent/Minilang_Agent.thy` intentionally dropped
  `Complex_Main`, and `Minilang` only imports `HOL.List` + `Auto_Sledgehammer` — no `Main`,
  hence no `real`/`rat`/`complex`/`GCD`/coercion).

Already committed & pushed (submodule `main`): `cb685a8` (removal of the `comment`
mechanism — **verified NOT responsible for anything in this report**), `d75291a` (golden +
doc follow-ups; note this commit **swept in other agents' staged files**).

Known-unrelated remaining test failures: 8 semantic/embedding-DB drift
(`AbbrevQuery`, `ExperienceMemory`, `Query*`, `RetrieveFact`, `SemanticKNN_*`) and 3
environment (`ForkProviderConflict`, `Rewrite_LoopingForkCtxt` need the `openai` pip
package; `Define_DeleteOracle` hits an agent quota give-up).

---

## 18. Key symbols to grep

| symbol | file | role |
|---|---|---|
| `NonLeaf_Node._resulting_state_of_child` | `model.py` | the aliasing |
| `Node.resulting_state` | `model.py` | |
| `StdBlock._resulting_state_of_all_children` → `_state_before_ending_` | `model.py` | last child |
| `Minilang_State.reset` / `.initialized` | `model.py` | destructive delete / the predicate |
| `Node._cancel`, `StdBlock._cancel` | `model.py` | **the culprit** |
| `NonLeaf_Node._failed_predecessor_id` | `model.py` | blame attribution |
| `NonLeaf_Node._refresh_all_children_after` | `model.py` | the cascade |
| `GlobalEnv._body_affects_siblings` | `model.py` | the trigger (`= True`) |
| `Session._prefetch_worker_premises` | `model.py` | **the unguarded consumer** |
| `Session.resolve_context_at` | `model.py` | **the guarded consumer — copy its doctrine** |
| `Session._edit_verdict`, `_amend_preserves_worker`, `_dispatch_blocked_by` | `model.py` | the `edit`-boundary discipline the cascade bypasses |
| `Role_Worker.target`, `WorkerHandle.run_until_yield` | `model.py` | the anchor / the driver |
| `_request_tool_logic`, `_run_struggle_checkpoint` | `mcp_http_server.py` | the two prefetch call sites |
| `ProofMCPHTTPServer.call_tool` (`except Exception: sys.exit(1)`) | `mcp_http_server.py` | the amplifier (**do not touch**) |
| `DISABLE_REQUEST_GENERAL_LEMMAS` | `config.py` | why the path is dormant |
| commit `184d718` | git | the workaround that was just reverted |
