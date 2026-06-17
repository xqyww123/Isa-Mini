# Layered Success / Forced-BFS — Implementation Plan (Consensus)

Status: **FROZEN — all design decisions resolved with the user (2026-06-16).**
Consensus across the three debate threads, then every open question (E1 predicate
/ E2 Suffices / E3 wording / S2 trigger tails / frontier scope / quickview
folding) settled. Ready to implement per §8.

All citations are `file:symbol` or `file:line` against the source as read on
2026-06-16. Line numbers drift; prefer the symbol.

---

## 1. Overview & mechanism

Layered success is a **pure display + effective-completion overlay** on top of
the existing AoA proof tree. The *layer* of an `Obvious` (Sledgehammer leaf) is
the number of `Have` / `Obtain` / `GoalNode` ancestors on its root→node path. A
shared `Runtime.bfs_level` counter governs which failed `Obvious` are *papered*:
a failed `Obvious` whose `layer() >= bfs_level` is rendered as a soft
"accepted-for-now" annotation instead of an error, and is treated as
effective-finished by a **paper-aware** variant of `unfinished_nodes`. After a
planner `edit`, if the only thing keeping the proof open is papered `Obvious`
(the effective-unfinished set is empty but real work remains), `bfs_level` is
bumped so the next-shallower layer is exposed for real, and one encouragement
line is printed. Real completion, termination, caching, assembly, and worker
success ALL stay bound to the **real** (un-papered) judgement — papering never
closes a goal and never short-circuits `is_proof_finished()`.

---

## 2. Confirmed design decisions (USER-CONFIRMED — do not relitigate)

1. **Pure display overlay.** `Obvious` still runs real `HAMMER` and still FAILS;
   we override only the DISPLAY and the *effective-completion* judgement, via a
   `paper_level` parameter threaded into `unfinished_nodes`. **No `sorry`-closing
   of goals**; `status` / `_is_trivial` are never mutated by the overlay.
2. **Coexist** with the existing worker / subagent dispatch architecture; do not
   replace worker dispatch.
3. **Bump** loops `bfs_level += <step>` until the effective-unfinished set is
   non-empty (work exposed) OR the proof is truly finished.
4. **Layer** counts `Have` / `Obtain` / `GoalNode`; level starts at 1;
   comparison uses `>=`.

> NOTE on decision 4 (RESOLVED 2026-06-16): the threads flagged a "floor
> conflict" — a top-level GoalNode can never be delegated (`mcp_http_server.py:1375`,
> `target.parent is psr` refused) so a papered layer-1 Obvious would be
> undelegatable. **Reassessed and NOT a hard contradiction:** the bump loop
> un-papers layer 1 within the *same* edit (level ratchets 1→3 on the first
> paper-closable skeleton, exposing layers 1+2 for real), and a layer-1 Obvious
> is meant to be proved inline anyway (it never qualifies for delegation). User
> CONFIRMED the original quadruple: **`layer() >= level`, start `bfs_level=1`,
> bump step `+= 2`** (so exposed in pairs (1,2),(3,4),…), GoalNode counted. The
> encouragement line first fires only once the whole scope is paper-closable
> (all remaining gaps are deep Obvious), which is the intended "your idea works"
> moment. Remaining predicate sub-choices: **E2** (count Suffices?) and the
> GoalNode taxonomy detail — see §6.

---

## 3. Detailed implementation (per file:symbol, exact logic)

All edits are in `IsaMini/AoA/model.py` unless noted. The implementation channel
agreed by all three threads: **thread `paper_level` (and a `papered` carrier)
through `unfinished_nodes`; `paper_level=None` reproduces today byte-for-byte.**
`is_proof_finished` (model.py:4931) is **NEVER** touched.

### 3.1 `Runtime.bfs_level`  (model.py:`Runtime.__init__`, 9649)

Add one field:

```python
self.bfs_level: int = 1   # start=1, user-confirmed; monotone non-decreasing
```

Invariants:
- Read **only** by (a) the display overlay (§3.5) and (b) the bump helper (§3.6).
  Never by assemble / proof_cache / `is_proof_finished` / `interrupt` /
  `newly_completed_topmost` / `_subtree_stats`.
- A fresh `Runtime()` is constructed per major session (model.py:9722, only when
  `parent is None and runtime is None`). Cache replay constructs its own major
  session ⇒ a fresh `Runtime` ⇒ `bfs_level=1`, and the bump loop lives only in
  `edit_message` which does not run on replay. **E4 (replay freshness) is thus
  resolved: replay renders at level 1, real-equivalent.** No reset needed at the
  replay entry.

### 3.2 `Obvious.layer()` and `Obvious._is_papered()`  (new methods on `class Obvious`, model.py:6635)

```python
def layer(self) -> int:
    n = self.parent
    count = 0
    while n is not None:
        if isinstance(n, (Have, Obtain, Suffices, GoalNode)):
            count += 1
        n = n.parent
    return count
```

`Have` (model.py:7869), `Obtain` (8210), `Suffices` (8117), `GoalNode` (5281).
**E2 RESOLVED 2026-06-16: `Suffices` IS counted** — it is a goal-reframing
block structurally symmetric to `Have`/`Obtain` (its own body + closing leaf),
and counting it aligns `layer()` with `_subgoal_level` (which also bumps on
Suffices, 8124). The minimum layer of any `Obvious` is 1 (it always sits under at
least the top-level GoalNode `root.sub_nodes[1..]`).

```python
def _is_papered(self, level: int) -> bool:
    if self.status.status != EvaluationStatus.Status.FAILURE:
        return False
    if self._under_branch_exhaustiveness():
        return False
    return self.layer() >= level    # >=, user-confirmed
```

`_under_branch_exhaustiveness()` walks ancestors and returns True iff any
ancestor `node` satisfies `isinstance(node.parent, Branch) and node is
node.parent.sub_nodes[0]`. This is **Branch-specific** and **structural**, never
by string id: `Branch.__init__` sets `_initial_goal_index = 0` (model.py:8798)
so its `sub_nodes[0]` is the "exhaustiveness of the case split" obligation;
`SubgoalMaker.__init__` sets `_initial_goal_index = 1` (model.py:5528), so
`CaseSplit` / `Induction` (`CaseSplit_Like`, 5921) have **no** id-`0`
obligation. Papering the exhaustiveness obligation would let an unproven
case-split claim completeness, so it is excluded.

### 3.3 `unfinished_nodes` signature (two channels)

Change the signature on every override to:

```python
def unfinished_nodes(self, ret: set['Node'],
                     paper_level: int | None = None,
                     papered: list[bool] | None = None) -> None:
```

Rationale for the **two-channel** carrier (reconciles Thread-1's "accumulator
set / dataclass" with Thread-3's `list[bool]`): guard (b) below needs to know
"does this subtree contain ≥1 papered Obvious?", but papered Obvious are exactly
the nodes *excluded* from `ret`, so `ret` cannot answer it. A single mutable
one-element `list[bool]` flag (`papered[0]`) is the minimal carrier and keeps the
whole pass **O(n)** (no second descent, no O(N²) re-walk). We deliberately do
NOT use a `set` of papered nodes: nothing downstream needs their identity, only
existence-within-subtree, and a per-block local flag OR'd up answers that in one
walk.

`paper_level=None` ⇒ `papered` is irrelevant and the body is identical to today.

#### 3.3.1 `Node.unfinished_nodes`  (model.py:3788, base/Leaf)

```python
if not _status_can_continue(self.status.status):
    ret.add(self)
```
Unchanged logic; just accept and ignore the two new params (they are only
consulted by the `Obvious` and `StdBlock` overrides).

#### 3.3.2 `NonLeaf_Node.unfinished_nodes`  (model.py:4538)

```python
super().unfinished_nodes(ret, paper_level, papered)
if self.status.status != EvaluationStatus.Status.COMMENTED:
    for child in self.sub_nodes:
        child.unfinished_nodes(ret, paper_level, papered)
```
Pure pass-through.

#### 3.3.3 `GlobalEnv.unfinished_nodes`  (model.py:9240)

```python
for child in self.sub_nodes:
    child.unfinished_nodes(ret, paper_level, papered)
```
Pure pass-through. (A posed-but-unproved declarative `Have` in the global env has
no papered Obvious tail, so guard (b) is False and it correctly stays in `ret`.)

#### 3.3.4 NEW `Obvious.unfinished_nodes`  (override on `class Obvious`, near 6646)

```python
def unfinished_nodes(self, ret, paper_level=None, papered=None) -> None:
    if paper_level is not None and self._is_papered(paper_level):
        if papered is not None:
            papered[0] = True
        return                      # treated as effective-finished
    super().unfinished_nodes(ret, paper_level, papered)   # -> Node (Leaf) self-add
```

#### 3.3.5 `StdBlock.unfinished_nodes` — the propagation + guard  (model.py:4941)

This is the load-bearing site. The block currently self-adds based on its OWN ml
state (`opening()` + uninitialized-or-pending), which reflects reality — so
skipping papered Obvious in children is NOT enough; the paper must **propagate
up** through this self-add. Final agreed form:

```python
def unfinished_nodes(self, ret, paper_level=None, papered=None) -> None:
    nbefore = len(ret)
    papered_local = [False]
    super().unfinished_nodes(ret, paper_level, papered_local)   # recurse children FIRST
    if papered is not None and papered_local[0]:
        papered[0] = True                                       # OR up to caller

    if self.status.status == EvaluationStatus.Status.COMMENTED:
        return
    if self.opening() and (not self._state_before_ending_.initialized()
                           or self.has_pending_goal()):
        if (paper_level is not None
                and not self.has_pending_goal()        # (R3) load-bearing
                and self._paper_closes(ret, nbefore, papered_local)):
            return                                     # paper-closed: do not self-add
        ret.add(self)
```

`_paper_closes` (new helper on `StdBlock`):

```python
def _paper_closes(self, ret, nbefore, papered_local) -> bool:
    # (a) no descendant of self was added to ret by the child recursion
    #     (all children effective-finished under paper)
    # (b) self's subtree contains >= 1 papered Obvious
    return (len(ret) == nbefore) and papered_local[0]
```

Notes reconciling the three threads:

- **Guard term `not self.has_pending_goal()` (Thread-1 R3).** `has_pending_goal`
  (model.py:4892) returns the real leftover `leading_goal` of
  `_state_before_ending_`, independent of child membership, and returns `False`
  when uninitialized (4897-4898). So suppression is permitted **only** when the
  block is open purely because its ending op never ran
  (`not _state_before_ending_.initialized()`), NEVER when a real `leading_goal`
  survives. This correctly handles the `&&&` multi-`shows` case: a leftover
  conjunct lives in `leading_goal`, so `has_pending_goal()` is True and the block
  self-adds — the unsound "last-child-is-papered-Obvious" proxy is **dropped**.
- **Guard (a) uses `len(ret) == nbefore`** rather than a descendant membership
  scan: because the child recursion ran first and papered Obvious were already
  excluded by §3.3.4, any addition to `ret` during the recursion is a genuinely
  still-open descendant. This is O(1) and order-independent.
- **Guard (b) `papered_local[0]`** prevents falsely hiding a genuinely-incomplete
  block that has *no* papered Obvious (empty body, or all-success non-closing
  steps): such a block keeps `papered_local[0] == False` and self-adds as today.
- **Generic across every StdBlock** (Thread-2 R9 / Thread-1 R1). `GoalNode` is a
  `StdBlock` subclass, so intermediate case `GoalNode`s also drop when papered.
  `SubgoalMaker.opening()` (model.py:5917) returns `False`, so its own self-add
  is dead and Branch/CaseSplit/Induction leave the unfinished set automatically
  once their child `GoalNode`s do.

#### 3.3.6 `CaseSplit_Like._paper_closes` override  (model.py:`CaseSplit_Like`, 5921)

A case-split / induction has **no** exhaustiveness obligation child (§3.2), so
the only thing keeping an all-failed induction honest is its per-case `Obvious`
failures — which papering would erase. Therefore add requirement (c):

```python
def _paper_closes(self, ret, nbefore, papered_local) -> bool:
    if not super()._paper_closes(ret, nbefore, papered_local):
        return False
    # (c) every case child is REALLY proved (paper_level=None)
    return all(c.is_proof_finished() for c in self.sub_nodes)
```

(`self.sub_nodes` are the case `GoalNode`s; `is_proof_finished()` is real,
model.py:4931.) **Accepted consequence (not a bug):** papering never advances the
ratchet past a CaseSplit/Induction — the maker stays effective-unfinished until
its cases are really proved. The ratchet still advances on shallower work
elsewhere because the propagation guard is per-block. `Branch` keeps the base
(a)∧(b); its `sub_nodes[0]` obligation is never papered (§3.2) so it self-adds
under reality until really discharged.

### 3.4 `Session.proof_scope_unfinished_nodes`  (model.py:10729)

Add the param, forwarding to the scoped root:

```python
def proof_scope_unfinished_nodes(self, paper_level: int | None = None) -> 'set[Node]':
    unfinished: 'set[Node]' = set()
    papered: list[bool] = [False]
    self.proof_scope_root.unfinished_nodes(unfinished, paper_level, papered)
    return unfinished
```

Default `None` ⇒ every existing call site
(`newly_completed_topmost` 10749, and any other no-arg caller) stays REAL
byte-for-byte. **`newly_completed_topmost` is left calling it no-arg (real)** —
see §4 (isolation) for why it must never go paper-aware. The bump helper (§3.6)
passes `paper_level=runtime.bfs_level` explicitly; this is the **single non-None
call site**, a grep-enforceable invariant.

> Reconciliation: Thread-2/3 proposed keeping `proof_scope_unfinished_nodes`
> no-arg and calling `proof_scope_root.unfinished_nodes(...)` directly from the
> bump helper. Thread-1 proposed adding the param here. **Consensus: add the
> param with a `None` default** (cleaner single entry point; honesty is preserved
> by the `None` default + the grep invariant that the only non-None caller is the
> bump helper). Either is sound; we pick the param form for one rendering entry.

### 3.5 Display overlay (Obvious-only)

`_print_evaluation_status` (model.py:3504) and its quickview twin
`_print_evaluation_status_quickview` (3528) live on `Node` and render NOTHING for
SUCCESS, the "Error:" block for FAILURE. The papered token must therefore be
**added** (not merely "suppressed"), and only for `Obvious`.

The display path does NOT thread `paper_level` (`Node.print` / `quickview` /
`quickview_proof_scope` at model.py:11053 do not carry it). Consensus: the
**display overlay reads `runtime.bfs_level` via `the_session()`**, gated to the
major session, at the `Obvious` render site only. This is the *one* sanctioned
ambient read of `bfs_level` (the unfinished/bump logic always threads it). Add
`Obvious`-specific overrides that call super for the non-papered case:

**E3 WORDING — FINAL (user-approved 2026-06-16).**

- **print status line** (full `print`):
  `status: outstanding — accepted for now but you will be asked for more details before the proof is complete.`
- **quickview marker**: the compact tag is `[outstanding]`. The **first time**
  `[outstanding]` appears in a given quickview render, append a one-time
  explanation; subsequent papered Obvious in the same render show only
  `[outstanding]`. First-appearance explanation:
  `[outstanding] = accepted for now; keep going and clear all remaining Error steps first. You will be asked for more details before the proof is complete.`
- **bump encouragement line** (§3.6, user-approved FINAL):
  `Good! Your overall proof structure works. But there are still some outstanding proof goals that are not yet proved and need more detail. Now prove them.`

```python
# on class Obvious
_OUTSTANDING_LINE = ("status: outstanding — accepted for now but you will be "
                     "asked for more details before the proof is complete.")
_OUTSTANDING_TAG = "[outstanding]"
_OUTSTANDING_FIRST = ("[outstanding] = accepted for now; keep going and clear "
                      "all remaining Error steps first. You will be asked for "
                      "more details before the proof is complete.")

def _print_evaluation_status(self, indent, file) -> None:
    if self._papered_for_display():
        print_indent(indent, file)
        file.write(self._OUTSTANDING_LINE + "\n")
        return
    super()._print_evaluation_status(indent, file)

def _print_evaluation_status_quickview(self, indent, file) -> None:
    if self._papered_for_display():
        sess = the_session()
        print_indent(indent, file)
        if not sess.shown_outstanding_hint:
            sess.shown_outstanding_hint = True
            file.write(self._OUTSTANDING_FIRST + "\n")
        else:
            file.write(self._OUTSTANDING_TAG + "\n")
        return
    super()._print_evaluation_status_quickview(indent, file)

def _papered_for_display(self) -> bool:
    sess = _session_var.get(None)
    return (sess is not None and sess.is_major
            and self._is_papered(sess.runtime.bfs_level))
```

- **`shown_outstanding_hint` flag** — a per-render `Session` flag (like the
  existing `showed_fill_hint` / `shown_HAVE_fact_names`). Add it to `Session.__init__`
  (default `False`) and reset it in `_reset_view_state` (model.py:10660) alongside
  the other one-shot view flags, so the long explanation prints once per quickview
  render and `[outstanding]` alone thereafter. (Full `print` always uses the long
  `status:` line — no first/rest distinction there.)
- **Obvious-only / blocks render real status.** Block headers
  (`GoalNode`/`Branch`/`CaseSplit` `_print_header`) are untouched and always show
  REAL status (Thread-2 R10). "Papering as subtree-paper-finished" (lying about a
  block's own status line) is **rejected**.
- **`_print_subagent_hint` (model.py:6688) is KEPT** for papered Obvious
  (Thread-2 R4 / Thread-3 R6). A papered Obvious is exactly a deep failed Obvious
  that should be delegated; suppressing the dispatch affordance would gut the
  on-demand subagent model. **Display semantics RESOLVED 2026-06-16:** the papered
  Obvious renders as a soft "accepted-for-now · still to prove / delegable"
  annotation, NOT a bare green "success" — this preserves the dispatch signals.
  The exact WORDING is still **E3** (deferred to the user).
- **Quickview folding stays REAL — do NOT make it paper-aware (RESOLVED
  2026-06-16).** `_quickview_children_compressed` (model.py:4256) folds runs of
  ≥5 children where `not changed and not does_quickview_need_detail()`. Leave
  `Node.does_quickview_need_detail` (3492, `changed or not
  _status_can_continue(status)`) and `StdBlock`'s (5005) UNTOUCHED: a papered
  Obvious has real status FAILURE ⇒ `does_quickview_need_detail()` True ⇒ it (and
  its still-`opening()` parent block) is **always shown expanded**, never folded,
  each carrying its `<PAPERED_TOKEN>` line. Folding keys off `status`/`changed`,
  never the rendered text, so the token wording never affects folding. Accepted
  consequence: a large skeleton shows every papered step (no "focus-the-frontier"
  collapse). The newly-exposed frontier after a bump is shown either way (still
  real FAILURE). The paper-aware-folding alternative was considered and rejected
  (would need a paper-aware `does_quickview_need_detail` + a deferred-vs-ok fold
  summary replacing `"... all ok"` at model.py:4269).

### 3.6 Shared bump helper (prompts.py)

All FOUR post-tool tails share one helper (S2 resolved: bump on all four).
Today each of `edit_message` (prompts.py:92), `deleted_steps_message` (138),
`comment_message`, and `subagent_overall` (209) independently writes
`Outline:` + `quickview_proof_scope(1,file)` + the unfinished/Congratulations
check. Factor that duplicated tail into one helper that all four call (for the
major session it bumps; for a worker it is truthful, never papers, never bumps).

```python
def _bump_and_render_outline(session, file) -> bool:
    """Render the paper-aware Outline for the MAJOR session, ratcheting
    runtime.bfs_level to expose the shallowest real work. Returns `finished`
    (bound to REAL completion only). Prints one encouragement line iff a bump
    actually happened this call."""
    rt = session.runtime
    real = session.proof_scope_unfinished_nodes()          # paper_level=None, HONEST
    if not real:
        file.write("Outline:\n")
        session.quickview_proof_scope(1, file)
        file.write("Congratulations! All goals are proven.\n")
        return True

    bumped = False
    if session.is_major:
        eff = session.proof_scope_unfinished_nodes(paper_level=rt.bfs_level)
        while not eff and _tree_has_papered_obvious(session.proof_scope_root, rt.bfs_level):
            rt.bfs_level += 2            # +2, user-confirmed (exposes layers in pairs)
            bumped = True
            eff = session.proof_scope_unfinished_nodes(paper_level=rt.bfs_level)

    file.write("Outline:\n")
    session.quickview_proof_scope(1, file)                  # display overlay reads bfs_level
    if bumped:
        file.write("Good! Your overall proof structure works. But there are "
                   "still some outstanding proof goals that are not yet proved "
                   "and need more detail. Now prove them.\n")
    return False                                            # finished = not real
```

`_tree_has_papered_obvious(root, level)` is a one-shot walk returning
`any(isinstance(n, Obvious) and n._is_papered(level) for n in subtree)`.
(Could be folded into the same `unfinished_nodes` pass via the `papered`
carrier; the explicit walker is acceptable, O(n), and keeps the loop legible.)

Each of the four tails (`edit_message`, `deleted_steps_message`,
`comment_message`, `subagent_overall`) replaces its inlined
`Outline:`/quickview/unfinished/Congratulations block with:

```python
finished = await _bump_and_render_outline(session, file)
# (each tail keeps its own surrounding bits: _render_auto_intro_warning,
#  root.reset(), the trailing non-error failure note, etc.)
```

Because paper rendering is always-on for the major session, the
`quickview_proof_scope` inside the helper renders papered automatically — no
flag is passed. For a worker, `is_major` is False so the `bumped` block is
skipped and `quickview_proof_scope` renders truthfully (workers also skip
papering at the Obvious render site, §3.5).

- **Termination / Congratulations stay bound to REAL** (`real` empty). The
  caller `_edit_tool_logic` (mcp_http_server.py:269) acts on `finished` →
  `session.interrupt()` exactly as today.
- **Encouragement dedup** is the local `bumped` flag — immune to `root.reset()`
  re-arming any latch (Thread-2 R5). No once-per-session flag.
- **Bump step `+= 2`** (USER-CONFIRMED). Starting from `bfs_level=1`, levels take
  odd values 1,3,5,… and layers are exposed in pairs: a layer-`L` Obvious is
  un-papered once `level > L`, so (1,2) expose at level 3, (3,4) at level 5, …
  This matches the "one conceptual row = a block layer (Have/Obtain) + its
  Obvious layer" intuition. Termination: `_is_papered(level)` is
  monotone-decreasing in `level`; once `level > max layer` nothing is papered so
  `eff == real ≠ ∅` and the loop stops; `bfs_level` is bounded by the smallest
  odd number `> max_layer`.

---

## 4. Edge cases & handling

| Case | Handling |
|---|---|
| **Nested blocks** | The `StdBlock` guard (§3.3.5) propagates paper upward through each block's own self-add; an outer block paper-closes only when (a) no still-open descendant remains AND (b) its subtree has ≥1 papered Obvious AND (R3) it has no real `leading_goal`. |
| **SubgoalMaker container GoalNode** | `SubgoalMaker.opening()` (5917) is `False`, its self-add is dead; it leaves the unfinished set automatically once child GoalNodes do. No special case. |
| **Branch exhaustiveness GoalNode** | Never papered (`_under_branch_exhaustiveness`, §3.2): `Branch.sub_nodes[0]` (`_initial_goal_index=0`, 8798). Structural test, not string id. |
| **CaseSplit / Induction** | No exhaustiveness child; `CaseSplit_Like._paper_closes` adds requirement (c): every case child REALLY finished. Ratchet never advances past an unproven case-split (accepted). |
| **Suffices** | **Counted** in `layer()` (E2 resolved): symmetric to Have/Obtain, aligns with `_subgoal_level` (8124). |
| **multi-goal `&&&` (multi-`shows`)** | A leftover conjunct lives in `_state_before_ending_.leading_goal`; `has_pending_goal()` True ⇒ block self-adds (never paper-closed). The discarded "last-child" proxy would have been unsound here. |
| **empty / non-closing blocks** | Guard (b) `papered_local[0]` is False ⇒ block self-adds as today; not hidden. |
| **`_is_trivial`** | The overlay NEVER reads/writes `_is_trivial` or `status`. Separately, fix the latent amend bug (D4 below): `NonLeaf_Node._amend_child` (4609-4611) constructs `gn.factory(config)` (running `Obvious.__init__`'s `GoalIsNontrivial` check at 6637) BEFORE clearing `self._is_trivial = None` at 4611. Move the clear to immediately *before* `new_node = gn.factory(config)`. This is a pre-existing bug the feature only makes more reachable; it is independent of `paper_level`. Golden run required (E-test). |
| **caching / assemble** | Cache replay builds a fresh `Runtime` (level 1) and never runs the bump loop (edit_message only). `proof_cache.py` / `assemble()` emit real HAMMER ops; they read REAL status, never `bfs_level`. |
| **termination isolation** | `is_proof_finished` (4931) untouched; Congratulations / `interrupt` bound to `real` (paper_level=None). |
| **`newly_completed_topmost` isolation** | Stays no-arg / REAL (model.py:10749). If it ran paper-aware, a papered subtree would be announced "proved" and latch `_completion_announced=True` (10780), *swallowing the genuine later completion* (10779-80). Intended consequence: the Outline may render papered-green while no "newly completed" line is announced — accepted. |
| **`_subtree_stats` / quickview counts** | These compute via `is_proof_finished()` (4938) → REAL. Counts stay honest even while the Outline shows a papered token. (The two threads that proposed precomputing a paper-aware `U` set for stats are NOT adopted: keeping stats real avoids O(N²) and a second `bfs_level` channel, and matches the "honest counts, soft token" stance.) |
| **worker scope** | Workers render `paper_level=None` (truthful); only the major session papers/bumps. See §5. |

---

## 5. Coexistence with worker / subagent dispatch + scope (S1)

**Architecture rebase (all three threads, verified).** The plan's original
`Role_Plan` / `stage` / `PLANNING` / `FINISHING` / `_collect_failed_obvious_parents`
/ "auto Worker-per-failed-Obvious" framing describes a **removed** architecture.
Verified: the role ADT is stageless — `Role_Major` (model.py:9622),
`Role_Worker` (9628), `Role_Interaction` (9637); there is no `Role_Plan`, no
`stage`, no `is_planning`. `_collect_failed_obvious_parents` exists only in docs
(`CLAUDE.md`, `docs/DEVELOP.md`), zero hits in code. Dispatch is **on-demand**:
the agent reads the rendered failure + `_print_subagent_hint` and chooses to call
the `subagent` tool. The feature rebases onto this model — which is exactly why
keeping the subagent hint on papered Obvious (§3.5, R4/R6) is essential.

**S1 resolution — papering is a property of a render *call*, never a session
flag.**
- `Session.is_major` / `is_worker` are **@property** (model.py:9924/9934) — use
  `session.is_major`, NO parens. (Both earlier transcripts wrote `is_major()`;
  corrected.)
- Workers: `proof_scope_root = role.target` (model.py:10665); worker success =
  `target.is_proof_finished()` (REAL); worker rendering, `newly_completed_topmost`,
  final assemble/termination ALL use `paper_level=None`. Workers never read
  `runtime.bfs_level`.
- Only the major session bumps, via the shared helper called from all four tails
  (`edit_message` / `deleted_steps_message` / `comment_message` /
  `subagent_overall`); it is the single caller passing a non-None `paper_level`.
- **Why this is coherent under a globally-shared `bfs_level`:** `bfs_level` only
  monotonically increases and gates DISPLAY + the major's effective-completion
  judgement only. A worker's concurrent real progress (mutating the shared tree)
  can only make the major *under-paper* (fewer nodes qualify as papered once they
  really succeed), never *over-paper*. No shared mutable papering state exists.

**Doc correction (independent of this feature):** `IsaMini/AoA/CLAUDE.md` (the
`_collect_failed_obvious_parents` / FINISHING / `Role_Plan` section) and
`docs/DEVELOP.md` are stale and should be corrected in a separate docs pass.
Surface to the user; do not silently rewrite as part of this feature.

---

## 6. Resolved sub-decisions + OPEN QUESTIONS FOR USER

### Resolved (with rationale)

- **Carrier shape** = single mutable `list[bool]` flag `papered` threaded
  alongside `paper_level` (not a `set`, not a dataclass). Minimal, O(n), nothing
  downstream needs papered-node identity. (Reconciles Thread-1 vs Thread-3.)
- **`proof_scope_unfinished_nodes` gains `paper_level=None`** (vs direct
  `unfinished_nodes` call from the helper). Single rendering entry; honesty
  guaranteed by the `None` default + grep invariant (only the bump helper passes
  non-None). (Reconciles Thread-1 vs Thread-2/3.)
- **Stats stay REAL** (no precomputed paper-aware `U`): honest counts + soft
  token, avoids O(N²) and a second `bfs_level` channel.
- **`newly_completed_topmost` stays REAL** — prevents latch-swallowing the real
  completion.
- **`_print_subagent_hint` kept** on papered Obvious.
- **Display overlay reads `bfs_level` via `the_session()` at the Obvious render
  site only**, gated `is_major`; this is the one sanctioned ambient read.
- **Bump step `+= 2`** (USER-CONFIRMED; exposes layers in pairs).
- **E4 (cache replay freshness) resolved in code:** fresh Runtime per major
  session ⇒ level 1 on replay; no reset needed.

### Decisions (ALL RESOLVED 2026-06-16 — nothing left open)

- **E1 — RESOLVED 2026-06-16.** User confirmed `layer() >= level`, start
  `bfs_level=1`, bump step `+= 2`, GoalNode counted. The "layer-1 undelegatable
  floor" is not a hard conflict: the bump loop un-papers layer 1 on the first
  paper-closable skeleton (level 1→3, exposing layers 1+2 for real), and a
  layer-1 Obvious is proved inline (never delegated) anyway. Hardcode `>=`,
  start=1, `+= 2`. (Remaining sub-detail: the GoalNode taxonomy in (d) below.)

  - **TAXONOMY (sub-detail of E1, default chosen, confirm if you disagree).**
    `layer()` counts every `isinstance(n, GoalNode)` ancestor (the literal
    "GoalNode 的数目"), which includes case/induction/branch case-children but NOT
    `SubgoalMaker` containers (`SubgoalMaker` is `GoalContainer+StdBlock`, not a
    `GoalNode` subclass) and NOT the Branch exhaustiveness obligation for paper
    purposes (it is excluded by `_under_branch_exhaustiveness`, §3.2). **Default:
    count all `GoalNode` instances.** No further action unless you want only
    "proof-carrying" subgoals.

- **E2 — RESOLVED 2026-06-16: count `Suffices`.** `layer()` counts
  `Have`/`Obtain`/`Suffices`/`GoalNode` (§3.2). Aligns with `_subgoal_level`.

- **E3 — RESOLVED 2026-06-16 (all wording final).** print status line =
  `status: outstanding — accepted for now but you will be asked for more details before the proof is complete.`;
  quickview tag = `[outstanding]` with a one-time first-appearance explanation per
  render (`shown_outstanding_hint` flag, §3.5); bump encouragement =
  `Good! Your overall proof structure works. But there are still some outstanding proof goals that are not yet proved and need more detail. Now prove them.`

- **S2 — RESOLVED 2026-06-16: bump on ALL FOUR tails.** The bump (and the
  paper-aware Outline) fire after `edit`, `delete`, `comment`, AND `subagent`
  (worker-return) tails for the major session. Paper RENDERING is always-on for
  the major session regardless of tail (it is a pure function of `is_major` +
  `bfs_level`, §3.5), so the tree never flickers between papered/real across tool
  calls; the bump LOOP is invoked from all four tails via the shared helper
  (§3.6). Workers (non-major) never paper and never bump.

- **E3-frontier (O3) — RESOLVED 2026-06-16: keep GLOBAL.** `bfs_level` stays a
  single global counter on the Runtime. Known limitation accepted: with multiple
  top-level goals, a level bumped while proving goal 1 will paper deep Obvious in
  a freshly-started goal 2 (`root.sub_nodes[2]`) with zero work done there.
  Single-goal proofs are unaffected. If this leak proves harmful in practice,
  revisit by keying `bfs_level` per top-level GoalNode id (deferred, not now).

---

## 7. Testing & golden-YAML protocol

**Hard rule (repo + AoA CLAUDE.md, project memory):** NEVER modify, regenerate,
overwrite, or delete any `Tests/*.yml` golden without explicit user approval —
the test passing again is not authorization. Surface the `.diff`
(`Tests/<name>.diff`, `<name>.actual.yml`), explain why, wait for approval.

- **Purity assertion (ships as a test, not prod code).** With the feature wired
  but the real path exercised (`paper_level=None` everywhere, or `bfs_level`
  pinned absurdly high so nothing papers), `_write_newly_completed` +
  `_subtree_stats` + every existing golden output MUST be byte-identical to
  feature-off. This proves the `None` path is untouched and every current
  `Tests/*.yml` stays green with no edits. Run the full existing suite first;
  any non-identical `.diff` is a regression to fix in code, NOT a golden to
  update.
- **New behavior** (papered token, bump, encouragement) gets its OWN dedicated
  `.thy` fixtures (NEVER share a `.thy` between two `@model_test`s) and NEW
  user-approved goldens. Author cases per the AoA test framework: drive the tree
  by hand, dump `root.print`/`root.quickview`, render the paper-aware Outline,
  and assert effective vs real unfinished counts
  (`root.unfinished_nodes(s, paper_level=K)` vs no-arg). Required new cases:
  (1) single layer-N papered Obvious renders token + effective-finished;
  (2) StdBlock propagation: papered Obvious paper-closes its `Have`;
  (3) guard (b): empty/non-closing block NOT hidden;
  (4) `&&&` multi-shows: block NOT paper-closed (`has_pending_goal`);
  (5) CaseSplit: not paper-closed until cases really proved;
  (6) Branch exhaustiveness Obvious never papered;
  (7) bump loop ratchets and prints encouragement once;
  (8) worker render is truthful (`paper_level=None`).
- **D4 `_amend_child` reorder** must pass the FULL existing golden suite before
  bless (it changes a side-effect ordering; `factory` reads only
  `config.parent._is_trivial`, so it appears safe — but confirm via golden run).
- Run `../../test_AoA.py -f NAME > /tmp/aoa.txt 2>&1`, one at a time, foreground.
  `remote_error` == a golden diff mismatch (read the on-disk `.diff`).
- **ML side:** this feature touches only Python (`model.py`, `prompts.py`). If
  any `.ML` is touched, ask the user to restart the REPL server (stale compiled
  ML otherwise).

---

## 8. Step-by-step implementation order

1. **Predicate / frontier / display-semantics / E2 / S2 RESOLVED** (E1: `>=`,
   start 1, `+= 2`, count all GoalNode; **E2: count Suffices**; frontier: global;
   display token = `outstanding`, all wording FINAL (E3, §3.5/§3.6); **S2: bump on
   all four tails**). **ALL design decisions are now closed** — the plan is fully
   specified; proceed straight to coding.
2. **D4 fix (independent):** reorder `NonLeaf_Node._amend_child` (model.py:4609-
   4611) to clear `self._is_trivial = None` before `new_node = gn.factory(config)`.
   Run the full golden suite; confirm byte-identical. (Latent bug, not feature.)
3. **Signature threading:** add `paper_level=None, papered=None` to
   `Node.unfinished_nodes` (3788), `NonLeaf_Node` (4538), `StdBlock` (4941),
   `GlobalEnv` (9240); pure pass-through. Add `paper_level=None` to
   `Session.proof_scope_unfinished_nodes` (10729). Run the full suite →
   byte-identical (purity assertion). This is the safe, behavior-neutral base.
4. **`Runtime.bfs_level`** field (9649), start value per E1.
5. **`Obvious.layer()` / `_is_papered()` / `_under_branch_exhaustiveness()`**
   (6635); `layer()` counts Have/Obtain/Suffices/GoalNode (E2), `>=`, start 1 (E1).
6. **`Obvious.unfinished_nodes` override** (§3.3.4) + **`StdBlock` propagation
   guard** (§3.3.5) + **`CaseSplit_Like._paper_closes`** (§3.3.6). Add new
   golden cases (2)-(6) — user-approved.
7. **Display overlay** (§3.5): `Obvious._print_evaluation_status` /
   `_print_evaluation_status_quickview` / `_papered_for_display`, token wording
   per E3. Keep `_print_subagent_hint`. Add golden case (1).
8. **Bump helper** `_bump_and_render_outline` in `prompts.py` (§3.6); factor the
   duplicated Outline tail out of all four message functions (`edit_message`,
   `deleted_steps_message`, `comment_message`, `subagent_overall`) and route each
   through it (S2: all four bump). Encouragement wording per E3. Add golden cases
   (7)-(8).
9. **Full regression:** run the entire existing suite; confirm every existing
   golden unchanged (purity). Surface any `.diff` to the user; never auto-update.
10. **Doc correction (separate, with user sign-off):** fix the stale
    `Role_Plan`/FINISHING/`_collect_failed_obvious_parents` text in
    `IsaMini/AoA/CLAUDE.md` and `docs/DEVELOP.md`.

---

### Key files
- `/home/qiyuan/Current/MLML/contrib/Isa-Mini/IsaMini/AoA/model.py`
- `/home/qiyuan/Current/MLML/contrib/Isa-Mini/IsaMini/AoA/prompts.py`
- `/home/qiyuan/Current/MLML/contrib/Isa-Mini/IsaMini/AoA/mcp_http_server.py`
- `/home/qiyuan/Current/MLML/contrib/Isa-Mini/IsaMini/AoA/CLAUDE.md` (stale arch — separate fix)
