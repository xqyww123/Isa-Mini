# D1 fix plan — terminate a sub-agent whose target fell into a dead region

> **Status:** plan only. NO code written. Awaiting user approval.
> **Date:** 2026-07-09
> **Line numbers drift** — every claim is anchored on a symbol name. Grep for it.

---

## 0. The bug, in one paragraph

`Minilang_State` is a *named snapshot* in Isabelle's server-side state table
(`agent_server.ML`: `val state = Unsynchronized.ref (Symtab.make [("$init", s0)])`).
Python holds only the name. `Node._cancel` calls `reset()` on the state it produced,
and `reset()` sends `IsaMini.reset_state` → `Symtab.delete_safe` — the snapshot is
**deleted server-side**.

A worker (sub-agent) anchors on `role.target` and reads `target.ml_state`. When a
refresh cascade cancels the worker's region, that state is destroyed. Any subsequent
ML call with that name hits `get_state` → `error "beginning_state_not_found"` →
`IsabelleError` → `ProofMCPHTTPServer.call_tool`'s `except Exception: sys.exit(1)` →
**the whole host process dies**.

**The trigger is `request_lemmas`' general-lemma path.** It is the ONE place a worker
can mutate the tree *outside* its own scope: a requested lemma must land BEFORE the
worker's target for the worker to see it, so it goes into the `GlobalEnv`. And
`GlobalEnv._body_affects_siblings = True` ⇒ any GlobalEnv change re-evaluates EVERY
top-level goal. If that re-evaluation makes an earlier step newly fail, everything
after it is `_cancel`ed — possibly including the requesting worker's own target.

Irony: the worker asked for a lemma *so it could see it*; granting the request
demolishes the ground it was standing on.

---

## 1. Why the obvious fixes were rejected (all considered, all dropped)

| Idea | Verdict |
|---|---|
| refcount / give each node its own state | ❌ The aliasing is not the bug. `c[i].resulting_state() IS c[i+1].ml_state` — the object's *producer* is `c[i]`. If `c[i]` never ran, the state is meaningless. Deleting it is correct. |
| `184d718`: comment out both `reset()` calls | ❌ Trades a loud crash for silent use of a stale proof state. Strictly worse in a theorem prover. (User directed the restore on 2026-07-09; both `reset()`s are ACTIVE in the working tree, uncommitted.) |
| Make the cascade skip parked subtrees | ❌ Semantically wrong. The worker's target state was derived from the OLD context; skipping re-derivation means the worker never sees the lemma it asked for. |
| Add an `initialized()` guard to `_prefetch_worker_premises` only | ❌ Insufficient. See §2. |
| Introduce a `DeadStateError` exception | ❌ **User rejected.** "We don't need a new exception, that only complicates things. We ensure it never happens." Verified: `Minilang_State.execute` ALREADY converts `beginning_state_not_found` → `InternalError` (not an `IsabelleError` subclass), so `Leaf._refresh_me_alone`'s `except IsabelleError → FAILURE` cannot swallow it. The assertion already exists. |
| Park the worker (suspend, resume later) | ❌ **User rejected as too complex.** Would need a new park point, a new event, a new yield variant, plus a decision on whether a dead-target parent must recursively park. |
| **Terminate the worker; parent may dispatch a fresh one** | ✅ **CHOSEN.** |

### 1.1 Why "skip the prefetch" is not enough

Question asked: *if `request_lemmas` finds the target pending, can we just not update
the contextual facts?*

**No.** The worker is still alive and its LLM will make another tool call. Its next
`edit` dies too:

1. `StdBlock._cancel` → `await self._state_before_ending_.reset()` — the target's
   footer snapshot is deleted, `_initialized = False`.
2. Worker calls `edit` → `StdBlock.append` → `ml_state = await self._state_before_ending_.clone(None)`.
3. `Minilang_State.clone` on an uninitialized source **does NOT send RPC** — it silently
   returns a fresh shell with a brand-new name `$N` that Isabelle has never heard of.
4. The new node's `_refresh_me_alone` → `_execute_opr(self.ml_state, …)` → `execute` sends
   `$N` → ML `get_state` → `beginning_state_not_found`.
5. `Minilang_State.execute` → `raise InternalError(…)` → `call_tool` → `sys.exit(1)`.

Also note `Session._edit_verdict` has **no status check at all** — only confinement
(don't leave your scope) and lock (don't touch another sub-agent). It does not care
whether the ground is dead.

⇒ The fix must **stop the worker**, not merely make it skip one call.

---

## 2. The chosen design (user's own, verbatim)

> "在 request lemmas 发现 the target node 死掉后,直接杀死所有挂载其上的 subagents,
> 然后返回一个报警作为 the parent agent's `subagent` tool 的返回。"
> 一路全都杀掉;一路杀,直到一个活着的 parent。

### 2.1 The worker terminates ITSELF (it cannot be killed from inside)

`_request_tool_logic` runs **in the worker's own coroutine**. Worker `W`'s target `2.3`
holds `2.3.worker_handle == W`'s handle. `W` calling `handle.aclose()` would
`self._task.cancel(); await self._task` — **W awaiting its own task = deadlock.**

So the mechanism is self-termination, copying the EXISTING `report`/surrender path
(`mcp_http_server.py`, search `WorkerSurrender(`):

```python
handle._event_queue.put_nowait(WorkerSurrender(detail=detail))
session.quit_info = Surrender(detail)      # terminal → the agent loop breaks
await session.interrupt()
```

`WorkerSurrender`'s own docstring: *"Terminal — the worker interrupts itself right
after emitting this."*

**Verified:** `WorkerHandle._wait_next_event`'s docstring guarantees a queued event
always wins over task completion (`put_nowait` synchronously resolves the pending
`queue.get()` future; FIFO callback ordering). So the dispatcher sees
`WorkerRegionDead`, never a `WorkerDone(success=False)` mis-rendered as
*"could not prove"*.

**Verified:** `ClaudeCode.interrupt` does NOT stop the loop. Its own comment:
*"The proof loop's exit is driven by the end-of-turn gate, NOT by this interrupt:
once `receive_response()` returns, the loop breaks on a terminal `quit_info`."*
⇒ the worker finishes the CURRENT tool call and returns its response, then breaks.
So `_request_tool_logic` must still `return (msg, is_error)` normally.

### 2.2 Cascading to nested sub-agents: ALREADY FREE

`WorkerHandle._run`'s `finally` (grep `Defensive: close any sub-agents`):

```python
finally:
    for child in self.target.sub_nodes:
        await child.aclose_all_subagents()
```

`aclose_all_subagents` is itself recursive. **Zero new code for "kill them all".**

### 2.3 Cascading UP to a living parent

`Root`-level cascades can kill worker `A`'s target AND nested worker `B`'s target at
once. So after `B` self-terminates and control returns to `A`, `A` must check ITS OWN
target and self-terminate too. Recursion bottoms out at the planner: `Role_Major` is
`@dataclass class Role_Major: pass` — **no `target` field**, `session.is_worker` is
False, so it always catches the control flow.

### 2.4 Nothing is lost but the LLM conversation

`NonLeaf_Node.aclose_all_subagents` docstring: *"cancel + detach, **keeping each
partial proof**. The nodes THEMSELVES STAY in the tree."* A worker's output IS nodes on
the shared tree (`_make_fork` sets the child's `root = parent.root`). Terminating a
worker cancels its asyncio task and detaches the handle; the proof steps remain.

Once the parent fixes the earlier step, the re-refresh rebuilds the whole subtree's
states, and a freshly dispatched sub-agent picks up from those steps.

**⚠ Precision:** a new `subagent` call goes through `_run_worker_on` → `WorkerHandle(node, session)`
→ `handle.start()` — a **brand-new worker with a brand-new LLM session**. The old
worker's reasoning is gone. The wording must say "dispatch a **new** sub-agent",
never "resume", because the handle was `_detach()`ed.

### 2.5 `_cancel` and `reset()` are NOT touched

They were always correct. The fix is entirely consumer-side.

---

## 3. The predicate

`_status_can_continue(s)` is literally `s is EvaluationStatus.Status.SUCCESS`
(`model.py`). So `not _status_can_continue(target.status.status)` covers both:

- **CANCELLED** — an earlier sibling/ancestor failed (`target.ml_state` was `reset()`)
- **FAILURE** — the target's OWN beginning op failed in the new context (e.g. the new
  lemma caused a name clash and its `Have` statement no longer type-checks). Here
  `target.ml_state` may still be live and nothing would crash — but the worker's goal
  no longer exists, so it must not continue either.

**This is the SAME predicate the dispatch gate already uses.** `_subagent_tool_logic`
(grep `That step was cancelled by an earlier failure`) separately rejects FAILURE and
CANCELLED before dispatching or resuming. Consistency: what you may not hand TO a
sub-agent, you may not let a sub-agent keep.

---

## 4. Changes

### `model.py`

**① `TechnicalFailure` quit type** (next to `Surrender` in the QuitInfo ADT):

```python
@dataclass
class TechnicalFailure:
    reason: ClassVar[str] = "technical_failure"
    is_terminal: ClassVar[bool] = True
    detail: str | None = None
```

Add to the `QuitInfo` union.

**No driver changes needed.** All four drivers only ever test
`isinstance(self.quit_info, (Restart, Refresh))` and break otherwise. Verified in
`driver_claude_code.py`, `driver_api.py`, `driver_openai.py` (since removed), `driver_codex.py`.

**No `toplevel` impact.** Per the ADT's own comment: *"The major/planner session's
value is what `toplevel` reports to ML; a fork's value dies with the fork."* Only
workers can reach this path (`Role_Major` has no target).

**② `WorkerRegionDead` event** — copy `WorkerSurrender`:

```python
@dataclass
class WorkerRegionDead:
    """The worker's target lost its usable proof state (its own op FAILED, or it was
    CANCELLED by an earlier failure). Terminal — the worker interrupts itself right
    after emitting this."""
    detail: str
```

**③ `WorkerYield.REGION_DEAD`** — copy `SURRENDERED`; extend the `kind` docstring enum.

**④ `run_until_yield` case** — copy `case WorkerSurrender()` verbatim:

```python
case WorkerRegionDead():
    await self.wait_finish()
    self._detach()
    return WorkerYield.REGION_DEAD(event.detail)
```

**⑤ `Session._terminate_if_region_dead`** — the shared helper, two call sites:

```python
async def _terminate_if_region_dead(self) -> bool:
    """If this worker's target no longer has a usable proof state — its own
    operation FAILED, or it was CANCELLED by an earlier failure — terminate the
    worker: notify the dispatcher via `WorkerRegionDead`, set a terminal
    `quit_info`, and interrupt. Returns True iff it terminated.

    No-op (False) for a non-worker and for a live target. Mirrors the
    `report`/surrender wind-down exactly (queue event + terminal quit_info +
    interrupt); the worker still finishes its current tool call, because
    `ClaudeCode.interrupt` only nudges the in-flight request — the loop breaks on
    the terminal `quit_info` at the end-of-turn gate.
    """
```

Body: guard `not self.is_worker` → False; guard `_status_can_continue(target.status.status)`
→ False; else build `detail`, `put_nowait(WorkerRegionDead(detail))`,
`self.quit_info = TechnicalFailure(detail)`, `await self.interrupt()`, return True.

`detail` (log-facing, developer audience — verified NOT shown to any LLM: `quit_info`
is only read as a boolean in `mcp_http_server.py`, and this path bypasses the
`_wait_next_event` branch that copies `quit_info.detail` into `WorkerDone.detail`):

- with a culprit (`target._cancelled_by` set):
  `target step {target} fell into a cancelled region (step {culprit} failed); cannot continue`
- without (`_cancelled_by is None`, i.e. the target's own op FAILED):
  `target step {target} failed in the updated context; cannot continue`

Ids rendered via `self._display_id(...)`.

### `mcp_http_server.py`

**⑥ `_request_tool_logic`** — TWO checkpoints. Revised after adversarial review; see §6c.

**⑥a (the one that matters) — after the general-lemma loop, BEFORE the constraints
block.** Concretely: right after `session.working_block = saved_working_block`
(mcp_http_server.py:1552) and before `if constraints:` (:1560).
`await session._terminate_if_region_dead()`; if True, skip the constraints block AND
the prefetch block.

Why here and not at the prefetch: if the worker emits
`WorkerRequestConstraints`, the DISPATCHER's coroutine runs
`Interaction_ReviewConstraint.answer` → `Have.add_constraints` (model.py:9142) →
`_refresh_me_alone` → `_refresh_the_beginning_opr` → `_execute_opr(self.ml_state, …)`
on the **dead input state**. That raises `InternalError` (NOT `IsabelleError`), so
`add_constraints`' revert-on-FAILURE (model.py:9143) never fires; nothing between
there and `call_tool`'s `except Exception: sys.exit(1)` catches it
(`_inline_interaction`, model.py:12971, catches only `Interaction_BadAnswer` /
`IsabelleError` / `ContinuingInteraction`). **The crash happens in the dispatcher's
coroutine while the worker is suspended at `await fut` — a check at the prefetch could
never run in time.** Terminating BEFORE the event is emitted is what prevents it: the
dispatcher only calls `add_constraints` in response to the worker's event.

**⑥b — immediately BEFORE `if any_scope_change:` (mcp_http_server.py:1573)**, covering
the constraints-only call (no general lemmas). The helper is a no-op if ⑥a already
fired.

Per review F2: at either point the response string is NOT yet assembled (assembly is
~1606-1620), and the code in between (`_write_newly_completed`, `proof_scope_unfinished_nodes`)
is ML-safe on a dead region — `has_pending_goal` short-circuits on `not s.initialized()`
(model.py:5744) before reading anything. So ⑥ must **skip prefetch + `refresh_YAML` +
`consume_new_scope_facts_notice` and fall through to normal assembly**, NOT early-return
(an early return would silently drop the newly-completed-substeps line).

**⑦ `_subagent_tool_logic`** — new `case "region_dead"` in `match outcome.kind`
(user-approved wording, verbatim):

```
The sub-agent on step {target} was terminated for a technical reason. This says
nothing about whether its proof approach was wrong — the steps it wrote remain in
the tree. You may dispatch a new sub-agent on this step to carry on.
```

**⑧ `_subagent_tool_logic`, recursion** — after the `match`, before returning the tool
response: `await session._terminate_if_region_dead()`. Covers "a nested worker's
`request` killed MY target too". Terminates at the planner (`Role_Major` has no target).

**⑨ `_run_struggle_checkpoint`** — TERMINATE, don't just skip. (User chose option (b)
on 2026-07-09, after review R4 showed that a bare `warn + return None` repeats the very
"skip one call but keep running" mistake §1.1 rejects: the worker's LLM would receive
the `delete` tool response and its next `edit` would clone the dead
`_state_before_ending_` → `sys.exit(1)`.)

Placement: at the top of the function, after the existing `isinstance(session.role,
Role_Worker)` / `handle is None` guards, BEFORE the expensive
`launch_interaction(Interaction_StruggleCheckpoint(...))` fork.

```python
if await session._terminate_if_region_dead():
    session.warn_AoA_opr(...)          # invariant break: should be unreachable
    session._reset_struggle_counters() # optional; the worker is dying anyway
    return None                        # `str | None`; None ⇒ nothing appended to the
                                       # delete tool's response (mcp_http_server.py:618)
```

The predicate lives ONLY in the helper — no duplication. `warn_AoA_opr` writes only to
`interaction.yaml` + logger (verified) ⇒ **not user-facing**, no wording approval needed.

**Reachability (proved during review, worth recording):** once ⑥a/⑧ are in, this branch
is unreachable. A worker's own `edit`/`delete` cannot kill its own target, because
(1) `_edit_verdict` confinement restricts it to strict descendants of its target
(model.py:12469); (2) an ordinary `StdBlock` has `_body_affects_siblings = False`
(model.py:5499) — only `GlobalEnv` is True (:10496) — so a change inside the target's
subtree never re-refreshes the target's siblings; (3) the target's own beginning op is
never re-run by a change below it. And the nested-worker case is caught by ⑧ at the
`subagent` boundary first. We terminate anyway: the unreachability rests on those three
invariants, and if any is ever relaxed this branch must fail loudly, not defer the crash
by one tool call.

**Note (corrects a review claim):** `_run_struggle_checkpoint` has exactly ONE call site,
inside **`_delete_tool_logic`** (mcp_http_server.py:617) — not the edit path. The edit
counter still increments, but the checkpoint only fires on a `delete` call.

**Note:** the struggle-checkpoint *park* is already safe — its only wake-up is the
dispatcher calling `subagent`, which must pass the CANCELLED/FAILURE gate. `resolve_resume`
has exactly two call sites (verified by grep): the `subagent` tool, and
`run_until_yield`'s in-loop constraint resume.

### `config.py`

**⑩ `DISABLE_REQUEST_GENERAL_LEMMAS = True → False`** — user approved (2026-07-09).
Historical note: added by `a10a958` (2026-06-26) purely to save tokens
(*"the path that auto-dispatches a headless prover sub-agent and burns tokens"*),
**two days before** the crash was discovered (`184d718`, 2026-06-28). The two are
unrelated; the gate merely happened to also close the crash path.

⚠ Flipping it re-blesses goldens `RequestLemmasAutoProve`, `RefuteOrSurrender`,
`RequestFinishesTarget` (all re-blessed to the gated no-op behaviour on 2026-07-09).
Per repo rule, each golden diff needs explicit user approval. **Order: do ①–⑨, run the
tests, bring the diffs to the user, then flip ⑩.**

---

## 5. What is NOT in scope

- **`constraints` half of `request`.** Its in-loop resume (`run_until_yield` calls
  `resolve_resume` itself, bypassing the `subagent` gate) merges into the SAME
  `if any_scope_change:` prefetch, so ⑥ covers the crash. Whether that bypass should
  itself change is a separate question. **Not decided by the user.**
- **The stale-state hole.** When `c[j]` FAILS (not cancels), `c[j+1].ml_state` is
  neither rewritten nor reset: it keeps last round's snapshot, `initialized()` is
  still True. `Session.resolve_context_at` will silently hand that stale state to a
  planner `query`. Independent bug; do not mix in.
- **`Minilang_State.clone`'s uninitialized branch** does not clear `assign_to._initialized`
  — same family of "silent staleness". Independent.
- **`sys.exit(1)`** in `call_tool` — user decided explicitly: do not touch.

---

## 6. Verification plan

- `python -u ../../test_AoA.py -f Request 2>&1 > /tmp/aoa_req.txt` (worker/request cases),
  then the subagent family. Never two runs in parallel (shared REPL on 6666). Always
  redirect — output is huge.
- `remote_error` ALWAYS means a golden diff; read `Tests/<name>.diff` / `<name>.actual.yml`.
- Known-unrelated existing failures (do not chase): 8 semantic/embedding-DB drift
  (`AbbrevQuery`, `ExperienceMemory`, `Query*`, `RetrieveFact`, `SemanticKNN_*`);
  3 environment (`ForkProviderConflict`, `Rewrite_LoopingForkCtxt` need the `openai`
  pip package; `Define_DeleteOracle` hits an agent quota give-up).
- No `.ML` is touched ⇒ no REPL restart needed.

## 6b. EMPIRICAL EVIDENCE (probe `ProbeD1Cascade`, 2026-07-09, actually run)

A by-hand model test (`test.py::_test_ProbeD1Cascade`, fixture
`Tests/Test_ProbeD1Cascade.thy`) — no LLM, no worker loop, just the tree machinery.
Tree: `1 = Have A`, `2 = Have B { 2.1 = Have C1, 2.2 = Have C2 }`. Fake parked
`WorkerHandle`s on `B` (outer) and `C2` (nested, deliberately NOT a first child).
Trigger: `insert_before("2", <ill-typed Have>)` ⇒ predecessor FAILS ⇒ cascade.

Measured:

```
C1 top-level goal re-refreshed after GlobalEnv fill: 1 time(s)
--- after the cascade ---
C2 (nested worker target) status: cancelled
B  (outer worker target)  status: cancelled
C2.ml_state=DEAD                 <- nested worker's prefetch reads THIS
C1.ml_state=LIVE                 <- first child: LIVE but STALE
B.ml_state=LIVE                  <- outer worker's prefetch reads THIS
B._state_before_ending_=DEAD
C2._state_before_ending_=DEAD    <- worker's next `edit` clones THIS
B.worker_handle still attached: True    C2.worker_handle still attached: True
hB task cancelled: False                hC2 task cancelled: False
```

**Conclusions, in order of importance:**

1. **The status predicate (§3) is REQUIRED; an `initialized()` predicate would be WRONG.**
   The OUTER worker's target `B` is `CANCELLED` yet `B.ml_state` is **LIVE** — because
   `B`'s producer (the inserted node) FAILED rather than being `_cancel`ed, so nobody
   reset it. A guard on `target.ml_state.initialized()` would let the outer worker sail
   through prefetch and continue proving against a **stale context in a dead region**.
   `not _status_can_continue(B.status.status)` catches it. This **refutes** the
   `initialized()`-based guard that `D1_CANCEL_STATE_OWNERSHIP.md` §10.3 proposed, and
   answers its open question Q2 empirically: the two predicates do **not** coincide.

2. **⑧ (recursion to the parent) is necessary, not speculative.** One cascade cancelled
   BOTH the nested worker's target (`C2`) and the outer worker's target (`B`).

3. **"Skip the prefetch" would not have saved the outer worker.** `B.ml_state` is LIVE
   (no crash at prefetch), but `B._state_before_ending_` is **DEAD** — and that is
   exactly what `StdBlock.append` clones for the worker's next `edit` (§1.1). It would
   crash one tool call later.

4. **C3 confirmed: the cascade does NOT tear down workers.** Both handles stay attached,
   both tasks alive. The `edit`-boundary teardown discipline is genuinely bypassed.

5. **C1 confirmed:** a `GlobalEnv` fill re-refreshes the top-level goal exactly once.

6. **The §4 corollary holds:** a first child (`C1`) keeps a LIVE-but-STALE state. This is
   why the bug is intermittent, and it is an instance of the stale-state hole in §5
   (out of scope here).

Probe artifacts (NEW files, no existing golden touched): `Tests/Test_ProbeD1Cascade.thy`,
`Tests/ProbeD1Cascade.yml` (auto-written, since no golden existed), and the probe in
`test.py`. **Ask the user whether to keep the probe as a regression test or remove it.**

## 6c. ADVERSARIAL REVIEW (3 attackers + 2 rebuttal defenders, 2026-07-09)

### SURVIVED — must be fixed

**R1 (BLOCKER, confirmed by the rebuttal round).** `request` may carry BOTH
`general_lemmas` and `constraints` in one call (`tools/cc_request.jsonc` — independent
optional props, no `oneOf`; `mcp_http_server.py:1398` comment says so explicitly). The
general block (1460-1552) can cancel the worker's own target; the constraints block
(1560) then routes to the dispatcher, whose `add_constraints` executes the target's
beginning op from the dead input `ml_state` → `InternalError` → `sys.exit(1)`. This is
UPSTREAM of the old ⑥ at 1573, and it fires in the *dispatcher's* coroutine while the
worker sleeps at `await fut`. ⇒ fixed by **⑥a** above.

Narrower than first claimed (both narrowings verified): it crashes only when
(1) gate ⑩ is off, (2) the target is AMENDABLE (`Have` / `SetupRewriting`,
`can_add_constraints()` — model.py:9123/9268; a GoalNode/Obtain/Suffices takes the
`accept_restructure` PARK branch at model.py:3242 and never calls `add_constraints`),
(3) the target is CANCELLED with a **dead input state** (if it merely FAILED, its
`ml_state` is LIVE-but-stale per §6b, `add_constraints` runs, sets FAILURE, and reverts
cleanly), and (4) the dispatcher accepts the constraint.

**R2 (doc defect, not a code defect).** §2.1's stated rationale was WRONG. The worker's
post-terminate safety does NOT come from `interrupt()` (fire-and-forget, and neither
`call_tool` nor `_check_tool_permission` nor `permission_control` reads `quit_info`). It
comes from `ToolExecutor.execute`'s first statement `if session.check_budget(): return
("Budget exhausted…", True)` (mcp_http_server.py:2513) plus `check_budget`'s first line
`if self.quit_info is not None: return self.quit_info.is_terminal` (model.py:12101).

⇒ **`TechnicalFailure.is_terminal = True` is load-bearing.** Set it to False and the
host-kill returns, with no test catching it. Document this at the dataclass. (This is
the same rail `Surrender` already rides — not a new mechanism.)

**R3 (doc defect).** The committed sibling `D1_CANCEL_STATE_OWNERSHIP.md` now
contradicts this plan: its §13.1 recommends reusing the `.initialized()` guard, §13.4/
§14-Q1 recommend a producer-side `_cancel` teardown, and §14-Q4 is marked "BLOCKING —
do this first". §6b's probe **empirically refutes** §13.1/§14-Q2: the predicates do not
coincide, and `.initialized()` would let a cancelled-but-live-stale target through.
⇒ Mark that doc's §13/§14 as superseded; record the Q2 answer.

### PARTIALLY SURVIVED — user decision required

**R4.** ⑨ (`_run_struggle_checkpoint`) as specified only `warn + return None`, which is
the very "skip one call but keep running" pattern §1.1 rejects. The defender PROVED the
branch is currently unreachable: `_edit_verdict` confinement (model.py:12469) plus
ordinary `StdBlock._body_affects_siblings = False` (model.py:5499; only `GlobalEnv` is
True at :10496) means a worker's own edits can never cancel or fail its own target; and
⑧ catches the nested-worker case at the `subagent` boundary first. Options: keep
warn-only (user's earlier choice), or call the helper (one line, strictly safer,
consistent with ⑥/⑧).

### REFUTED — no action

**R5.** "A cross-branch parked worker (W1 on goal 1) whose region a sibling worker's
cascade killed is leaked and gets a misleading resume error." A parked worker touches
nothing until woken; the only wake-up is the `subagent` tool, which rejects a
CANCELLED/FAILURE target at mcp_http_server.py:1783-1790 **before** `resolve_resume`.
`Session.close`'s `root.aclose_all_subagents()` (model.py:11846) collects it at
wind-down. This is the intended "stay parked until the region is repaired" behaviour.

**R6.** "⑧ is mis-placed; `subagent_overall` would crash first." It renders from cached
Python state; `_print_footer` prints "Error: Evaluation cancelled" on `not initialized()`
(model.py:5765). No ML call. **R7.** "`_run`'s finally / `_settle_costs` / `sub.close()`
touch a dead ml_state." They do not. **R8.** "`_wait_next_event`'s queued-event-wins is
racy." `if queue_get in done: return` is checked first (model.py:13294). **R9.**
"`wait_finish` may hang." Same shape as the working `WorkerSurrender` path.

### Residual — CLOSED (investigated 2026-07-09)

*Concern:* while the worker sleeps at `await fut` in the constraints block, the
DISPATCHER is live and `Interaction_ReviewConstraint` is **non-forking**. Could the
dispatcher interleave a GlobalEnv-mutating `edit` before answering, crashing
`add_constraints` on a freshly-dead state?

**No — structurally prevented, not incidentally.** `_inline_interaction` sets
`session._nf_pending_interaction` (model.py) for the duration, and
`_check_tool_permission` (mcp_http_server.py) refuses every tool in `_MUTATION_TOOLS`
= {`edit`, `delete`, `subagent`, `cancel_subagent`, `request`} while it is set. That
frozenset's own comment names this exact path ("its constraint path (an amend on a
delegated block) mutates the tree"). A second, independent guard: `_run_tool_via_channel`
refuses to start a new channel task while `_suspended_task` is parked. The permission
check reads the field synchronously, so it does not depend on tool calls being
serialized. `Interaction_ReviewConstraint` is the only non-forking interaction in the
worker-yield loop; `Interaction_ReviewRefutation` forks with a restricted tool list.

## 6d. CODE REVIEW OF THE IMPLEMENTATION (3 attackers + 1 defender, 2026-07-09)

**Found and fixed:**

- **BLOCKER — the fix introduced a NEW host-kill.** `_request_tool_logic`'s headless-prover
  consumer asserts `outcome.kind in {proved, could_not_prove, surrendered, refute_accepted}`.
  The new terminal kind `region_dead` was missing. Reachable: a headless prover raises a
  `constraint` on its own global `Have`; the requester accepts; `add_constraints`'
  `_refresh_all_after_me` leaves that target non-SUCCESS; ⑥b fires; the prover yields
  `region_dead`; the assert trips → `AssertionError` → `sys.exit(1)`. (The general-lemma
  route was refuted: a lemma whose own op fails is deleted and the target restored before
  the check.) **Fixed** by widening the set; it falls into the existing `else`, which
  deletes the node and relays the reason.
  `Root.delete` is safe on a dead node: its refresh loop skips any refresh point with
  `not _status_can_continue(rp.status.status)` (model.py) — the same predicate this fix uses.
- **MINOR — blank id in ⑨'s warn.** `_display_id` is relative to the session's scope root,
  which in a worker IS the target ⇒ `""`. Now uses the absolute `target.id`.
- **Docstring typo** (`target.status` → `target.status.status`).
- **Reuse** — the wind-down triple (queue event + terminal `quit_info` + `interrupt`) was
  duplicated between `_terminate_if_region_dead` and `report`'s surrender/refute paths.
  Extracted as `Session._wind_down_worker(quit_info, event=None)`; all three now share it.

**Refuted, no action:** the idempotence guard cannot swallow a needed termination
(`check_budget` short-circuits before any tool logic runs, so the helper is never reached
with a foreign terminal `quit_info`); `wait_finish` cannot deadlock (the worker never
awaits the dispatcher); no spurious "all goals proven" (`Node.unfinished_nodes` adds every
non-SUCCESS node, so `finished` is always False on a dead target); ⑧'s placement after
`subagent_overall` is fine (that renders from cached Python state, no RPC); `node` in the
`region_dead` case is the redirected target; `handle is None` is a deliberate assert;
`TechnicalFailure` breaks no driver (all four test only `isinstance(quit_info, (Restart,
Refresh))`) and cannot reach `toplevel` (worker-only; the planner has no target).

**Declined by the user:** naming the "fix the earlier step first" precondition in the
`region_dead` message (the dispatch gate already says it); adding a save/restore test to
keep the now-dead `DISABLE_REQUEST_GENERAL_LEMMAS = True` branch exercised.

## 7. Open risks (stated honestly)

- **The production trigger is still not reproduced.** The probe forced a predecessor
  failure via `insert_before`; it did NOT demonstrate that *adding a global lemma* can
  make a previously-succeeding step newly fail. That step of the chain remains inferred.
  (Plausible mechanisms: a duplicate fact name, a new simp/intro rule that loops, or a
  nondeterministic `Obvious`/sledgehammer timeout on re-execution.)
- **No regression coverage of the crash path exists today** (the gate made it dead code).
  Whether to add a `@model_test` that flips the gate inside the test (save/restore) is
  undecided.

## 8. Constraints for the implementer

- Shared working tree; other agents run concurrently. **Never** `git stash` / `checkout` /
  `reset --hard` / `clean`. Commit on `main`, never branch. **Always inspect
  `git diff --cached` before committing** — the shared index has silently carried other
  agents' staged files into a commit before.
- `contrib/Isa-Mini` is a git submodule.
- **Never modify a golden YAML without explicit user approval** — even when the new
  output is obviously right.
- The working tree already carries an UNCOMMITTED change: both `reset()` calls restored
  in `Node._cancel` / `StdBlock._cancel`. This fix depends on them being active.
