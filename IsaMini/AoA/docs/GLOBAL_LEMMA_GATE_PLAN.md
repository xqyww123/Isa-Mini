# Global-Lemma Delegation Gate — Implementation Plan (FOR REVIEW, rev. 3)

## Context

The AoA agent (`contrib/Isa-Mini/IsaMini/AoA`) drives Isabelle proofs by building a tree of
high-level ops. The **main agent** (the *major* session) is supposed to lay out high-level proof
structure and farm out hard sub-proofs to dispatched **sub-agents** (workers). The system prompt
already *suggests* this workflow (model.py:10137-10144), but nothing *enforces* it: the major agent
can — and does — interactively fill a global lemma's proof body step by step (the cheap default
path), derailing its main line of reasoning.

This plan adds a **gate**: when enabled, the major agent may **declare** a global lemma (write its
statement under `global`) and **delete** it, but it may **not** interactively edit the lemma's
dedicated **proof-body slots** (`global.N.k…`) — it is steered to dispatch a sub-agent (worker). The
gate is LOCATION-ONLY (see D5): it removes the cheap incremental path and steers toward delegation;
it does NOT forbid inline authoring (a full re-attached `proof` body via `amend global.N {proof:[...]}`
remains possible, deliberately costlier and not advertised).

This **replaces** the earlier "layered-success / forced-BFS" effort (the abandoned
`docs/LAYERED_SUCCESS_BFS_PLAN.md` and the `~/.claude/plans/make-a-detailed-plan-wiggly-pancake.md`
plan), dropped entirely.

Revisions: rev. 2 folded in a first 97-agent adversarial debate (dispatch-target computation,
predicate, SetupRewriting delegability, second prompt site). rev. 3 folds in a second 86-agent debate
(the opt-in-kwarg threading bug, a live-worker resume-hint edge case, two further prompt sites, and
documentation/verification precision).

## Locked design decisions

1. **Replaces** layered-BFS (not coexists). No papering / `bfs_level` / `_paper_finished` machinery.
2. **Scope = all four provable global declarations:** `Have`, `Obtain`, `SetupRewriting`, `Define`
   (the only `_is_declarative` classes that can sit under `GlobalEnv`; `Define` may carry a deferred
   obligation materialized as child `GoalNode`s — that body is gated too).
3. **Non-worker-only.** Predicate: `session.is_major and not session.is_worker and
   session.gate_global_lemma_proofs`. Correct in production (real worker → `is_worker`; interaction
   fork → `is_major` False, no regression) AND lets the test harness simulate a worker by in-place
   role-flip on the parent-less root session.
4. **Each driver self-specifies the gate** via a `Session` class attribute
   `gate_global_lemma_proofs` (NOT on `Runtime`): base `Session` default `False`; the DeepSeek driver
   (`APIDriver_DeepSeekV4`) overrides to `True`. No `Session.__init__` parameter, no `toplevel.py` / ML
   / env wiring. Workers and interaction forks are the same driver class, but the predicate
   (`is_major and not is_worker`) already excludes them, so no per-instance inheritance is needed; tests
   force the gate by setting the instance attribute directly.
5. **The gate is LOCATION-ONLY.** It blocks only body-slot edits (`fill`/`insert_before`/`amend`
   landing on `global.N.k` or strictly inside a global decl). `delete` is always allowed. It does NOT
   inspect op bodies — an inline `proof` in a declaration op is ACCEPTED, and `amend global.N
   {proof:[...]}` (re-attaching the whole body) is ACCEPTED and may be ITERATED. The prompt is
   delegation-first and intentionally NOT softened.
6. **SetupRewriting is made delegatable.** `SetupRewriting._nearest_goal_for_subagent` returns `self`
   (mirroring Have/Obtain); the base docstring (model.py:3837-3839) drops it from "non-delegatable",
   and the `_subagent_tool_logic` invariant comment (mcp_http_server.py:1386-1387) adds it to the
   enumeration. **This is an UNCONDITIONAL engine change, NOT behind the gate flag** (golden-safety
   argued in Verification).
- **DESIGN:** the gate's dispatch target is computed via `node._nearest_goal_for_subagent()` (NOT the
  raw enclosing-decl id), so the error message names a step `_subagent_tool_logic` will accept.

## Verified facts the design relies on

- **Declare vs. prove are separable.** `fill global.N` creates a `Have` *header* with `sub_nodes == []`
  (no body); the body is filled separately at `global.N.1`, … (evidence: `test.py:135-136`).
- **`GlobalEnv`** (`model.py:9165`) is `Root.sub_nodes[0]` (id `"global"`); it only accepts
  `_is_declarative` children: exactly `Have` / `Obtain` / `SetupRewriting` / `Define`.
- **Dispatch target resolution.** `_subagent_tool_logic` (mcp_http_server.py ~1361) resolves the step
  through `node._nearest_goal_for_subagent()` and rejects `None` ("That step has no enclosing goal to
  prove."). Per class: `Have`→self (7872), `Obtain`→self (8213), `GoalNode`→self (5293),
  `SubgoalMaker`→redirects UP (5520) so a direct-global `Define` → `GlobalEnv`→`None` (9167),
  `SetupRewriting`→`None` today (8014; D6 changes to self).
- **`SubgoalMaker._id_of_openning_prf_to_fill` returns None** (model.py:5915-5916): a `Define`
  exposes NO directly-fillable slot, so a valid Define body fill always lands at `global.N.k.x`
  strictly inside an existing child `GoalNode` (deferred path creates them at 7019-7032).
- **The driver *is* a `Session` subclass** (`LMDriver(Session)` → `APIDriver`/`ClaudeCode`); driver
  classes already carry config as class attributes (e.g. `APIDriver_DeepSeekV4.DEFAULT_MODEL`,
  `SUBAGENT_NESTING_DEPTH`), so the gate flag follows the same idiom — a class attribute the driver
  overrides. No constructor parameter / Protocol change is needed.
- **Recoverable errors** reach the agent via the `(msg, True)` return from `_edit_tool_logic`
  (`isError=True`) — like the existing `OUT_OF_SCOPE` / `LOCKED` messages.

## Design

### 1. The switch + the predicate
The gate is a **class attribute** each driver self-specifies (NOT a `Runtime` field, NOT a constructor
parameter):
```python
class Session:
    gate_global_lemma_proofs: bool = False   # base default OFF; drivers override

class APIDriver_DeepSeekV4(APIDriver):
    gate_global_lemma_proofs = True          # gate ON for DeepSeek
```
Read directly as `session.gate_global_lemma_proofs`. No `Session.__init__` change, no `toplevel.py` /
ML / env wiring. A worker or interaction fork is the same driver class (so it sees the same value), but
the predicate excludes it anyway, so no per-instance inheritance is required. Tests force the gate by
setting the instance attribute directly (`session.gate_global_lemma_proofs = True`).

**Gate predicate** at the call site: `session.is_major and not session.is_worker and
session.gate_global_lemma_proofs`.

### 2. The location predicate + dispatch-target computation (new helpers in `model.py`)
Module-level, next to `_is_strict_ancestor` / `_first_worker_in_ancestors`:
```python
def _is_direct_global_decl(n) -> bool:
    return isinstance(n, (Have, Obtain, SetupRewriting, Define)) and isinstance(n.parent, GlobalEnv)

def _enclosing_global_decl(node):
    n = node.parent
    while n is not None:
        if _is_direct_global_decl(n):
            return n
        if isinstance(n, GlobalEnv):
            return None
        n = n.parent
    return None
```
On `Session`, resolve the target like `_edit_verdict`, decide whether the edit writes into a global
decl's body, and compute the dispatch target via `_nearest_goal_for_subagent()` (mirroring
`_print_subagent_hint`, model.py:6696) so the message never names a step `subagent` would reject:
```python
def _global_lemma_gate(self, step, action) -> 'tuple[bool, Node | None]':
    if action not in ('fill', 'insert_before', 'amend'):
        return (False, None)
    try:
        node = self.root.locate_node(step); new_slot = False
    except NodeNotFound:
        parent = step.rsplit('.', 1)[0] if '.' in step else None
        if parent is None:
            return (False, None)
        try:
            node = self.root.locate_node(parent); new_slot = True
        except NodeNotFound:
            return (False, None)
    if new_slot and _is_direct_global_decl(node):
        return (True, node._nearest_goal_for_subagent())
    if _enclosing_global_decl(node) is not None:
        return (True, node._nearest_goal_for_subagent())
    return (False, None)
```
Behavior table (gate ON, major session):

| Action / target | blocked | dispatch_target |
|---|---|---|
| `fill global.N` (declare new lemma; parent is `GlobalEnv`) | no | — |
| `fill global.N` / `amend global.N` with inline `proof` | no | — (D5: inline accepted/iterable) |
| `insert_before global.N` (declare a sibling lemma) | no | — |
| `delete global.N` | no (delete ungated) | — |
| `fill global.N.1` (fresh body slot under a Have/Obtain/SetupRewriting) | **yes** | the decl `global.N` (returns self; SetupRewriting via D6) |
| `fill/amend/insert_before global.N.1.…` (body of Have/Obtain/SetupRewriting) | **yes** | `global.N` |
| body slot strictly inside a `Define`'s child GoalNode (`global.N.k`, `global.N.k.…`) | **yes** | the GoalNode `global.N.k` (returns self) |
| `fill global.N.1` *directly on a `Define`* (no fillable slot exists) | (True, **None**) | — (deliberate fall-through, see below) |

**On the `(True, None)` row:** a direct-global `Define` has no directly-fillable slot
(`SubgoalMaker._id_of_openning_prf_to_fill` is None), so this row is only reachable for an INVALID
fill (out-of-range, or an auto-proved Define with no deferred obligation). The call-site guard
`if blocked and target is not None` (§3) **deliberately** falls through to the normal fill-error path
here; the `target is not None` guard is therefore load-bearing, not merely defensive. Every VALID
Define body fill lands at `global.N.k.x` (new_slot=False) and resolves to the child GoalNode.

### 3. Gate call site (`mcp_http_server.py`, `_edit_tool_logic`)
After the existing `LOCKED` handling (~349) and before `Parse_Op_List` (~354):
```python
if session.is_major and not session.is_worker and session.gate_global_lemma_proofs:
    blocked, target = session._global_lemma_gate(abs_step, action)
    if blocked and target is not None:
        # `amend` does NOT LOCK on a descendant worker (it would tear down its own target's worker),
        # so a sub-agent may already be parked inside `target`. In that case steer to RESUME it
        # (mirror the LOCKED _resume_hint, mcp_http_server.py:332-335) rather than naming an
        # enclosing decl that `subagent` would then reject.
        live = _first_worker_in_subtree(target)
        dispatch_id = session._display_id((live.target if live is not None else target).id)
        error_msg = (
            "Declaring global lemmas is great though you shouldn't prove a global lemma "
            f"yourself. Dispatch a sub-agent with `subagent` on step {dispatch_id} to prove it.")
        session.log_tool_response(_tn, f"ERROR: {error_msg}")
        return (error_msg, True)
```
The error wording is the user-approved string (kept verbatim — the "shouldn't prove yourself" framing
is intentional, delegation-first, even though D5 technically permits inline authoring). When a live
worker is found in `target`, the resume-hint wording (also user-owned) replaces the dispatch step with
that worker's step. `_display_id` is identity for the major; no op-body inspection; no `EditVerdict`
change.

### 4. Make SetupRewriting delegatable (D6 — UNCONDITIONAL engine change)
`SetupRewriting._nearest_goal_for_subagent` (model.py:8014) currently returns `None` ("empty body,
not a goal"), but a SetupRewriting is a `StdBlock` with a real proof body when the equation is
nontrivial. Change it to `return self` (mirroring `Have`/`Obtain`, 7872/8213) so `subagent global.N`
delegates a worker scoped to it (the whole-goal guard does not trip — its parent is `GlobalEnv`, not
`root`). Two doc-only companions kept in lockstep so the codebase stays self-consistent:
- base-class docstring (model.py:3837-3839): drop SetupRewriting from the "non-delegatable" list.
- `_subagent_tool_logic` invariant comment (mcp_http_server.py:1386-1387): extend the enumeration to
  "Have / Obtain / Suffices / SetupRewriting / GoalNode, all StdBlock subtypes" (the following
  `assert isinstance(node, StdBlock)` still holds — SetupRewriting IS a StdBlock).

**Needs a REPL-backed test** that a worker dispatched on a global SetupRewriting can render and prove
its body (cannot be fully verified statically).

### 5. Prompt changes (FOUR major-facing sites, all flag-gated where role-shared)
The contradicted "prove the lemma yourself under `global`" guidance lives in several is_major-facing
places; with the gate ON they should read declare-then-dispatch. To keep flag-off byte-identical and
the worker view uncorrupted, **each rewrite is gated on the predicate** (`is_major and not is_worker
and gate_global_lemma_proofs`); flag OFF renders the current wording unchanged.
- `model.py:10144` — `system_prompt()` (drivers that provide a system prompt, e.g. ClaudeCode). The
  verb "prove it" is in the **shared** f-string arm; only " under `global`" is `is_major`-gated. HARD
  REQUIREMENT: do NOT edit the shared verb in place; gate the **whole sentence** by role using the
  `(... if self.is_major else ...)` idiom already at lines 10137-10140 (else the worker string breaks).
- `model.py:10242` — `_compute_initial_prompt()`'s no-system-prompt branch (e.g. Codex). Already
  whole-sentence-gated (the `planner_hint` variable), so the 10144 in-place hazard does not apply here.
- `mcp_http_server.py:1295-1297` (+ docstring 1239-1241) — the `Role_Major` arm of
  `_request_lemmas_tool_logic` ("formalize and prove the lemmas … directly under `global` … `fill
  global.N`"). This is the worker→planner channel (a parked worker asks the major to supply a helper
  lemma); the major authoring it is the same non-worker-major case covered by D3/D5. Reword to
  declare-then-dispatch when the gate is ON.
- `model.py:9237-9239` — `GlobalEnv._print_footer` ("formalize and prove them here … `fill
  global.N`"). This renders **role-unconditionally** (to workers too and into goldens), so its
  gate-aware rewrite MUST be gated on the same predicate to avoid changing the worker/non-gated view
  or any golden.

Preferred: factor the major lemma-guidance into one shared helper referenced by 10144 / 10242 / the
request_lemmas arm, so they cannot drift. The major-arm wording becomes "declare it as a `Have` node
under `global`, then dispatch a sub-agent to prove it"; the worker arm and flag-off path keep the
existing "prove it …". Per project memory, all four user-facing strings are surfaced for user approval
rather than authored autonomously.

## Files touched
- `model.py` — `Session.gate_global_lemma_proofs` class attribute (default `False`); `_lemma_guidance`
  helper; two module helpers + `Session._global_lemma_gate`; `SetupRewriting._nearest_goal_for_subagent`
  → self (8014) + base docstring (3837-3839); prompt sites 10144, 10242, and `GlobalEnv._print_footer`.
- `driver_api.py` — `APIDriver_DeepSeekV4.gate_global_lemma_proofs = True`.
- `mcp_http_server.py` — the gate block in `_edit_tool_logic` (~349); the invariant comment
  (1386-1387); the `Role_Major` `_request_lemmas_tool_logic` arm (1295-1297) + docstring (1239-1241).
- `Tests/` — new gate + delegation + D6-tripwire fixtures (see Verification).
(No `toplevel.py` / `SessionConstructor` Protocol change — the gate is a driver class attribute.)

## What is explicitly NOT changed
- No `Runtime` field (D4).
- No inline-`proof` rejection / no op-body inspection (D5). `amend global.N {proof}` iteration is allowed.
- `delete` stays ungated.
- The user-approved gate error string is kept verbatim (Q1).
- No layered-success / `[outstanding]` / `bfs_level` machinery.
- `_edit_verdict` and the honest unfinished-set logic are untouched.

## Verification
- **Purity (highest priority):**
  - The gate edit-block branch is guarded by `is_major and not is_worker and gate_global_lemma_proofs`;
    the snapshot suite constructs a **bare `Session`** (test.py:53), whose class attribute
    `gate_global_lemma_proofs` is the base default `False` (the DeepSeek driver's `True` override is
    never exercised by the suite), so the branch is never entered (Python `and` short-circuits). Even
    armed, no existing `_edit_tool_logic` test targets a `global.*` step (`_global_lemma_gate` returns
    `(False, None)` for every top-level target — top-level nodes' parent is `Root`, not `GlobalEnv`).
    NOTE ~33 tests DO drive `_edit_tool_logic` directly; purity rests on these guards, not on bypassing
    the tool logic.
  - The §5 prompt rewrites are all flag-gated (and the footer rewrite is predicate-gated), so flag-OFF
    renders byte-identically and the worker view is unchanged.
  - **D6 is the one UNCONDITIONAL change.** Still golden-safe: its only runtime route into a golden is
    the subagent hint (`_print_subagent_hint`, model.py:6696→6700), which (a) renders nowhere in the
    current suite (needs a FAILURE `Obvious` with `_subgoal_level >= 2`; `_SUBAGENT_HINT_DEPTH=2`; the
    hint phrase appears in zero goldens), and (b) cannot structurally reach a SetupRewriting because
    `_subgoal_level` increments only at Have/Obtain/Suffices (7880/8124/8220) — all of which return
    self and intercept the upward `_nearest_goal_for_subagent` walk before any SetupRewriting. The base
    docstring (3837-3839) and the invariant comment (1386-1387) are never rendered. Both existing
    SetupRewriting goldens place it at top level with SUCCESS, level-0 Obvious bodies.
  - The §5-edited strings live only in `system_prompt` (10144) / `_compute_initial_prompt` (10242) /
    the request_lemmas arm / the footer. NOTE `test.py:12155` DOES invoke a prompt builder
    (`retry_prompt`, captured in `Tests/NestedWorkerScope.yml:72`) — golden-safety rests on the edited
    strings being absent from `retry_prompt` and from every golden (verified) AND on the rewrites being
    flag/predicate-gated, NOT on "builders are never invoked". The new Session parameter is not
    serialized (no `__getstate__`/pickle/asdict path).
  - Therefore the **full existing golden suite must be byte-identical**. Run one at a time, foreground,
    redirected: `python -u ../../test_AoA.py -f NAME > /tmp/aoa.txt 2>&1`.
- **New gate cases** (tool-logic pattern, flag ON, per `SubagentSlotResolve.yml` style):
  (a) `fill global.N` declare → allowed; (b) `fill global.N.1` body of a Have → blocked, names
  `global.N`, AND assert `subagent global.N` is accepted; (c) `amend global.N` header / inline `proof`
  → allowed; (d) `delete global.N` → allowed; (e) declare with inline `proof` → allowed; (f) a `Define`
  deferred-obligation body (`global.N.k.x`) → blocked, names the child GoalNode `global.N.k`, AND
  assert `subagent global.N.k` is accepted; (g) a worker editing the same body → allowed — author with
  the in-place role-flip idiom but **set `Role_Worker.target` to the global decl node itself** (else
  `_edit_verdict` returns OUT_OF_SCOPE first and the test exercises confinement, not the gate skip);
  assert success, NOT OUT_OF_SCOPE and NOT the gate error; (h) a global `SetupRewriting` body → blocked,
  names `global.N`, AND assert `subagent global.N` is accepted (exercises D6); (i) major dispatches a
  worker on a nested node (e.g. `global.N.1.2`), then `amend global.N.1` → blocked, message names the
  live worker's step `global.N.1.2` (resume), NOT `global.N`.
- **D6 regression tripwire:** add a golden nesting a FAILED `Obvious` ≥ 2 levels deep inside a global
  `SetupRewriting` (intervening Have/Obtain add +1 each to `_subgoal_level`) to pin the new hint /
  dispatch target (formerly None → now naming the SetupRewriting). Turns the incidental D6 immunity
  into an audited tripwire. Needs user approval before blessing the `.yml`.
- **§4 delegation (REPL-gated):** verify on a live Minilang_AoA REPL that a worker dispatched on a
  global `SetupRewriting` can render and prove its body.
- **Logistics:** golden runs need a Minilang_AoA REPL on 6666 (not currently running); editing
  `model.py` requires killing `Isabelle_RPC_Host` so fresh code loads. Coordinate the restart with the
  user. Never edit/regenerate/delete a `Tests/*.yml` without explicit approval.

## Open items / notes
- Exact opt-in kwarg name (`gate_global_lemma_proofs`) and CLI surface to set it (one-liner); default off.
- Whether to delete/retitle the abandoned `docs/LAYERED_SUCCESS_BFS_PLAN.md` (separate approval).
- D5 residual (acknowledged, no action): the gate narrows HOW the major self-proves (removes the cheap
  step-by-step path) but not WHETHER (inline `amend global.N {proof}` remains possible, costlier and
  unadvertised). Truly preventing inline self-proving would require op-body inspection — out of scope.
