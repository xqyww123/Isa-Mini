# AoA Developer Guide

**AoA** ("Agent over AST") is the AI-agent framework that constructs Isabelle proofs
through the Minilang proof language. This document explains the design for people (and agents)
working *on* AoA.

> Scope: `contrib/Isa-Mini/IsaMini/AoA/` (Python) plus the ML wiring in
> `contrib/Isa-Mini/Agent/` and `contrib/Isa-Mini/library/proof.ML`.
> References use stable symbol names (`Class.method`, function names), never line numbers — line
> numbers drift. Grep for the symbol.

---

## 1. Mental model

An AoA run turns one Isabelle goal (the `by aoa` invocation) into a **proof tree** of high-level
operations. Two kinds of agent operate on that tree:

- a **planner** that lays out the proof structure (intro, case split, intermediate `have`s, …) and
  closes routine goals with Sledgehammer, and
- **workers** — sub-agents the planner dispatches to discharge individual lemmas that did not close
  automatically.

The agents never speak raw Isar. They emit **Minilang operations** (a small high-level vocabulary),
which the ML side executes against a live Isabelle proof state. Agents perceive the proof as a
YAML-shaped rendering (`proof.yaml`) and act through a handful of MCP tools (`edit`, `delete`,
`query`, `recall`, `report`, `request_lemmas`, `write_memory`).

---

## 2. The status invariant (read this first)

> **`node.status.status` is the status of the node's OWN operation. What "own operation" means —
> and therefore what SUCCESS tells you — is node-type-dependent. The status of a *node* is NOT the
> status of its *subtree*.**
>
> **The criterion for whether a (sub)tree is proved is ALWAYS: `unfinished_nodes(...)` is empty
> (`is_proof_finished()`).**

This is the most frequently misread part of the framework. Get it wrong and you will conclude that
unproved lemmas are proved.

Specifically:

- **`Leaf`** (`Obvious`, `Rewrite`, `Intro`, …): SUCCESS means *that leaf operation itself ran
  without error*. For `Obvious` (= `HAMMER`/Sledgehammer), that does coincide with "the goal was
  closed" — a Sledgehammer that finds no proof raises an `IsabelleError` → FAILURE, which is exactly
  what makes the planner dispatch a worker.
- **`StdBlock`** (`Have`, `Obtain`, …): the node's status reflects **only the block's initial
  (beginning) operation**, not the block's body. For `Have`, the beginning op poses the statement, so
  SUCCESS means *the specification is well-formed and the subgoal was opened* — it says nothing about
  whether the body discharges it.

So the leaf case can make SUCCESS *look* like "proved" (because `Obvious` SUCCESS really did close
its goal); for a block it does not. Whenever the question is "is this proved", do not look at
`status` at all — check `unfinished_nodes`.

### 2.1 The three values

`EvaluationStatus` carries `status ∈ {SUCCESS, CANCELLED, FAILURE}`, a `time`, and an optional
`FailureReason`:

| Value | Meaning |
|---|---|
| `SUCCESS` | The node's **own operation** succeeded. Leaf → the op ran cleanly. StdBlock → the **beginning op** applied cleanly; the block's residual goal may still be open and `sorry`-ed. |
| `FAILURE` | This node's **own operation** errored — a leaf op (e.g. Sledgehammer found nothing), or a block's beginning op (e.g. an ill-typed `have` statement that could not be posed). |
| `CANCELLED` | The node was **never evaluated** because an earlier sibling in its block failed. Rendered as "pending". |

A fresh node starts at `EVALUATION_NOT_YET` (a FAILURE, "Not yet evaluated"). Note that
`EvaluationStatus.Success(time, reason=None)` accepts a *leftover* reason — a SUCCESS node can still
carry a `FailureReason`.

### 2.2 Why a posed-but-unproved block is SUCCESS

`NonLeaf_Node._refresh_me_alone`, schematically:

```python
if can_continue:                                       # children + footer closed the goal
    self.status = EvaluationStatus.Success(...)
elif head_succeeded:                                   # head opened, but the body did NOT close it
    await self._skip_proof()                            # sorry_end_all the remaining obligation
    self.status = EvaluationStatus.Success(..., reason) # STILL success
else:                                                  # the HEAD itself failed
    self.status = EvaluationStatus.Failure(..., reason)
```

The middle branch is the trap. When a `Have`'s statement is posed (`head_succeeded`) but its proof
body is empty/open, `_skip_proof` → `sorry_end_all` cheats the remaining goal and the node is
recorded as **SUCCESS**. `FAILURE` is reached *only* when the beginning op itself could not be
applied. For `Leaf` nodes there is no head/body split: SUCCESS iff the single operation ran without
an `IsabelleError`.

### 2.3 How to actually test "is it proved?"

Use `is_proof_finished()` / `unfinished_nodes()`, never `status == SUCCESS`.

```python
def is_proof_finished(self) -> bool:
    s = set(); self.unfinished_nodes(s); return not s
```

`NonLeaf_Node.unfinished_nodes` adds a node — **even a SUCCESS one** — when it is still `opening()`
(`_closed_by is None`) **and** `has_pending_goal()` (its `_state_before_ending_` has a real
`leading_goal`, not the placeholder `True`). So:

> For a block, `status == SUCCESS` and `is_proof_finished()` are **orthogonal**. The former says the
> block's beginning op opened; the latter says every obligation in the subtree is discharged. A
> block can be SUCCESS yet unfinished. `unfinished_nodes` empty is the *only* completion criterion.

A worker scopes this to its own subtree via `Session.proof_scope_unfinished_nodes`, and worker
success is judged by `target.is_proof_finished()` — *not* by the target's status.

(`_changes_pending_goal`, declared on a few node classes, is **never read**. It is vestigial; ignore
it. Pending-goal detection goes entirely through `has_pending_goal` / `opening`.)

### 2.4 Why declarative nodes leak facts before being proved — by design

`_is_declarative` nodes (`Have`, `Obtain`, `Define`, …) publish their named fact to later steps
*regardless* of proof status, mirroring Isar `have name: P sorry` keeping `name` usable downstream.
`Have._fixed_facts_after_me` unconditionally adds `name : conclusion` to the hypotheses visible to
successors; there is no status guard. This is *why* the worker's "available declarations" list (§5)
deliberately surfaces posed-but-unproved SUCCESS declarations — the fact is genuinely in scope. The
unproved-ness shows up separately, through `unfinished_nodes`.

---

## 3. One Isabelle session, many states, many Python sessions

Three things are easy to conflate. They are different:

| Layer | What it is | Count |
|---|---|---|
| **Isabelle / REPL session** | one Isabelle process behind the `Connection` (Isa-REPL, default `127.0.0.1:6666`) | **1** per `by aoa` |
| **`Minilang_State`** | a *named* server-side proof-state snapshot (`name` = `$init`, `$1`, …) sharing the one `connection`; holds `leading_goal` | **many** — roughly per node, before/after |
| **Python `Session`** | an *agent context*: the planner, or a worker/interaction fork | **many** — planner + forks |

A worker is a separate Python `Session`, but it does **not** spin up a new Isabelle session or a new
proof tree. The driver's `_make_fork` sets the child's `root = parent.root`; `Runtime` is the
singleton shared across all Sessions operating on the same proof tree. Forks share the `Connection`,
the `Root`, and the `Runtime`.

`Minilang_State.execute` runs an operation by calling back into ML:
`connection.callback("IsaMini.proof_opr", (from_name, to_name, (cmd, arg)))`, which returns the new
flat goal + messages. `Minilang_State.clone` issues a `SKIP` to snapshot under a fresh name;
`Minilang_State.reset` calls `IsaMini.reset_state`.

---

## 4. Proof tree & node model (`model.py`)

### 4.1 Terms

`IsaTerm` keeps two views: `.unicode` for the agent, `.ascii` for the RPC. `str()` is intentionally
disabled (raises) so a wrong representation can't leak. Construct with `IsaTerm.from_isabelle(ascii)`
/ `IsaTerm.from_agent(unicode)`. `Context = (vars, tvars, hyps)`, `Goal = (context, conclusion)`,
`Goals = (context, [Goal])`.

### 4.2 Node hierarchy

A diagram lives as a comment in `model.py` near the top-level node classes. Summary:

```
Node (ABC)
├─ Leaf                                   single Minilang op (Obvious, Intro, Rewrite, …)
└─ NonLeaf_Node                           has sub_nodes, _closed_by
   ├─ StdBlock                            beginning_opr / ending_opr(=END) / _state_before_ending_
   │  ├─ Have (_is_declarative)
   │  ├─ Obtain (_is_declarative)
   │  ├─ Suffices
   │  ├─ GoalNode                         the steps of ONE subgoal
   │  └─ GlobalEnv                        id "global"; only _is_declarative children
   ├─ GoalContainer                       children are independent subgoals (emits NEXT)
   └─ SubgoalMaker(GoalContainer, StdBlock)   opens N child GoalNodes
      ├─ InferenceRule / SplitConjs / Branch / Define
      └─ CaseSplit_Like → CaseSplit, Induction
Root(GoalContainer, StdBlock)             sub_nodes[0]=GlobalEnv, [1..]=top-level GoalNodes
```

Node ids look like `"global.1"`, `"2.1"`. Each proof-operation class is registered with
`@proof_operation(name, ToolArg)` and compiles to a `Minilang_Operation` factory method (`HAVE`,
`OBTAIN`, `RULE`, `HAMMER`, `INTRO`, `SUFFICES`, `BRANCH`, `CASE_SPLIT`, `INDUCT`, `END`, `NEXT`,
`SORRY_*`, …). `Obvious` compiles to `HAMMER` (Sledgehammer/auto) — it is the planner's "close this
routine goal" move, and a failed `Obvious` is exactly what triggers worker dispatch.

### 4.3 Node lifecycle

Editing the tree (`root.fill` / `append` / `insert_before` / `amend`) mutates structure, then
`_refresh_me_alone` re-runs the affected node against its `ml_state`:

1. Run the **beginning operation** (`_refresh_the_beginning_opr`). If it errors → `head_succeeded =
   False` → node FAILURE; remaining siblings CANCELLED.
2. Run the **children** in order; the first non-SUCCESS child cancels the rest.
3. Run the **ending operation** (default `END`). If children + footer closed the goal →
   `can_continue` → SUCCESS. Else if the head had succeeded → `_skip_proof` sorrys the rest → still
   SUCCESS (see §2.2).

`GoalContainer` blocks cross-child refresh propagation so independent subgoals don't disturb each
other.

---

## 5. Sessions, roles, and worker dispatch

### 5.1 Roles

`Session.role` is one of (`model.py`, all `@dataclass`):

- `Role_Major` — the single continuous main/planner agent. **Stageless**: it runs real proofs
  throughout and delegates hard sub-goals on demand; there is no PLANNING/FINISHING stage.
- `Role_Worker(target, suggestions, useful_lemmas, worker_handle)` — proves one node (a `Have`/step).
- `Role_Interaction(pending, prompt, resume_id, mode)` — a fork answering a retrieval / choose-target
  / refutation prompt.

Predicates (all `@property`): `Session.is_major` (no parent), `is_worker`, `is_interaction` — there is
no `is_planning`. `Runtime` holds the shared `age`, depth limit (30), tool-call counters, and
`worker_max_tool_calls` (500).

### 5.2 On-demand worker dispatch

There is **no** staged finish sweep — no `complete_proof`, no `FINISHING` role, no
`_collect_failed_obvious_parents` (these names survive only in stale docs; zero hits in code). The
main agent runs real proofs throughout: it reads a rendered failed `Obvious` (plus its
`_print_subagent_hint` for deep ones) and *chooses* to delegate a sub-goal by calling the `subagent`
tool (`_subagent_tool_logic` in `mcp_http_server.py`). That handler redirects to the target's nearest
delegatable goal (`_nearest_goal_for_subagent`; the whole-goal case `target.parent is psr` is
refused) and forks a worker. Workers may themselves dispatch nested sub-agents.

`WorkerHandle` (in `model.py`, attached as `node.worker_handle`) owns the worker's asyncio task and an
event queue; `run_until_yield` drives it until it yields control back to the dispatcher.
A worker communicates back through events rather than dying:

- `WorkerRefute` — "this goal looks unprovable"; the worker *blocks* on a review future while the
  planner decides, preserving its context.
- `WorkerRequestLemmas` — "I need a background lemma" (via the worker-side `request_lemmas` tool);
  the worker *blocks* while the planner authors + proves helper lemmas, then resumes — *conditionally
  terminal*: if the new lemmas/constraints discharge the worker's whole target scope, the `request`
  response announces completion and the worker terminates (the interrupt handshake, like `edit`).
- `WorkerDifficulty` — emitted by the system struggle checkpoint when it detects a stuck worker;
  the worker *blocks* (PARK) while the dispatcher decides to continue or abandon (non-terminal).
  Shares the same `_pending_resume` slot + `resolve_resume` path as `WorkerRequestLemmas`.
- `WorkerSurrender` — "I give up" (terminal).
- `WorkerDone` — synthesised when the task ends; `success` reflects `target.is_proof_finished()`.

When a worker raises `WorkerRequestLemmas`, the **planner itself** authors and proves the accepted
helper lemmas into the global env (there is no separate lemma sub-agent / `LemmaDrive`); the worker
then resumes with them in scope. `WorkerHandle.aclose`, called from the session-close sweep
(`Session.close` → the `aclose_all_subagents` / `discard` recursion over the tree), guarantees no
worker is left blocked on a review future.

### 5.3 The worker's scoped view

A worker should see *only its sub-problem*, presented as a self-contained goal.
`Session.print_proof_scope` renders, for a worker:

1. the ambient logical context — `variables:` / type variables / `premises:` from `root.context`
   (the original goal's fixed vars and hypotheses), via `print_vars` / `print_hyps`;
2. `available declarations:` — preceding **declarative SUCCESS** siblings in `global_env` (named
   lemmas already in scope; remember from §2.4 these may be posed-but-unproved, which is correct);
3. the target goal (`print_goal`), whose own premises (from its `SUFFICES` / `fix` / `assume`) appear
   under `premises:`;
4. the target's own substeps under `proof:`.

The contextual facts becoming "premises of the goal" is realised at the Isabelle level by the
declarative node's beginning operation (e.g. `Have`'s `SUFFICES(fixes, assumes, conclusion)`), which
performs Isar `fix` / `assume`. The Python `Goal.context.hyps` mirror those local assumptions and are
rendered under the `premises:` banner. `Session.quickview_proof_scope` is the compressed analogue.

---

## 6. Drivers and tools

`LMDriver(Session)` (`language_model_driver.py`) is the base: `run()` dispatches by role, with two
retry layers (`_with_retry` for quota — 20-minute wait; `_retry_transient` — 1.5ⁿ backoff).

| Driver | Notes |
|---|---|
| `driver_claude_code.py` | **default** (`ClaudeCode`). Uses the Claude Agent SDK pointed at the singleton HTTP MCP server (`mcp_servers={"proof": {type: http, url}}`). |
| `driver_api.py` (`APIDriver`) | Owns its own chat loop; calls `Provider.chat()`; runs tools in-process via `ToolExecutor`; compacts context at ~80%. Concrete: ChatGPT, K2Think, … |
| `driver_openai_api/anthropic/gemini/codex.py` | Provider variants, lazily imported in `toplevel.py`. |

**Tools** (abstract ids in `model.py`) map to external names per driver: `edit`, `delete`,
`query` (search — incl. `kinds:["experience"]` for saved proof strategies), `recall` (read `proof.yaml`), `report` (refute/surrender),
`request_lemmas` (dual-role: a worker→planner channel, or a planner self-formalize hint),
`write_memory` (save a reusable experience; `_write_memory_tool_logic`), answer-*. The tool→operation logic is in `mcp_http_server.py`: `_edit_tool_logic` parses the agent's
`proof_operations` and dispatches to `root.fill` / `insert_before` / `amend`. Tool JSON schemas live in `tools/*.jsonc`.

The **MCP server** (`ProofMCPHTTPServer` in `mcp_http_server.py`) is a singleton, multi-session HTTP
server with per-session endpoints `/mcp/<session_id>`; `call_tool` sets the ambient session,
permission-checks, and delegates to a per-session `ToolExecutor`. `APIDriver` reuses `ToolExecutor`
directly (no HTTP).

---

## 7. Rendering & the agent's `proof.yaml`

Two renderings, both emitting YAML-ish text:

- **`print`** (full): `Root.print` / `Node.print` — root context, the GlobalEnv, then each GoalNode.
- **`quickview`** (compressed): `Node.quickview`; runs of ≥5 unchanged children collapse via
  `_quickview_children_compressed`.

Helpers in `model.py`: `print_vars` (banner `variables`), `print_hyps` (banner **`premises`**),
`print_goal`, `print_pending_goal` (banner **`pending proof goal:`**). The worker scope adds the
**`available declarations:`** banner (in `print_proof_scope`).

Agents read/write `proof.yaml`: drivers write it on init and `Session.refresh_YAML` rewrites it
through `print_proof_scope`; the `recall` tool reads it back.

---

## 8. Entry, RPC, and caching

- `by aoa` → the `method_setup aoa` in `Agent/Minilang_AoA.thy`; method body is
  `MiniLang_Agent_AoA.method` in `Agent/agent_server.ML`. Default driver from config
  `AoA_driver`.
- AoA is **one long-lived RPC command** `IsaMini.AoA` (ML builds `aoa_cmd` in `agent_server.ML`;
  Python handler `IsaMini_AoA`, decorated `@isabelle_remote_procedure("IsaMini.AoA")` in
  `toplevel.py`). Within it, **Python calls back into ML** repeatedly (`proof_opr`, `reset_state`,
  `lookup_fact`, `check_term`, …; ML callbacks defined in `agent_server.ML`).
- Registered as the Isa-REPL app `Minilang.AoA` (`REPL_Server.register_app`). A client advances the
  theory to the `by aoa` line and calls `run_app('Minilang.AoA')`. The status the app reports —
  `success` / `remote_error` / an `Agent_Give_Up` reason (`stuck` / `false_statement` /
  `resource_exhausted` / `surrender` / `restart`) — comes from the `AoA_REPL_App` wrapper in
  `agent_server.ML`.
- Caching (in `IsaMini_AoA`): Python SQLite (`proof_cache.py`) → ML Phi_Cache JSON → full agent run.
  Hits replay packed ops via `set_replay_mode` + `proof_opr` (`_replay_cached_proof`).
  The bool config `AoA_use_proof_cache` (default `true`, `Attrib.setup_config_bool` in
  `agent_server.ML`) gates only cache *reading*: set it `false` (`declare [[AoA_use_proof_cache =
  false]]`) to bypass both levels of lookup and always run the agent. Writing is unconditional — a
  finished proof is still stored into both levels (Python L1 SQLite + ML L2 Phi_Cache_DB) on success.

---

## 9. Tests

The cases live in `contrib/Isa-Mini/IsaMini/AoA/test.py` (plus `run_all_tests` at its bottom); the
runner entry point is `contrib/Isa-Mini/test_AoA.py`. A test **drives the proof tree by hand** — no
LLM, no tool calls, no network — and diffs the rendered output against a golden YAML. So the suite is
deterministic snapshot testing of the model and the renderer. A consequence: in test mode the *only*
thing that can fail is the golden comparison (see "`remote_error`" below).

### 9.1 How a run executes

`contrib/Isa-Mini/test_AoA.py` parses CLI args (exporting `TEST_FILTER` / `TEST_EXCLUDE` env vars),
starts a Python-side RPC host on a daemon thread (bound to `127.0.0.1:27182` — the channel ML calls
*back* into, distinct from the REPL on `6666`), then `asyncio.run`s `run_all_tests(repl_addr,
sh_timeout=…)`.

`run_all_tests` (in `contrib/Isa-Mini/IsaMini/AoA/test.py`):

1. Opens `Client(repl_addr, 'HOL')` to the REPL (default `127.0.0.1:6666`),
   `load_theory(['Minilang_AoA.Minilang_AoA'])`, then `record_state("init")` — a clean snapshot.
2. Filters `TESTS.values()` by the env-var patterns (§9.5).
3. **Per case:**
   - `rollback('init')` — per-case reset (one long-lived Isabelle session; **not** a restart).
   - `repl.file(Tests/<file>, line, 0, cache_position=False, use_cache=False)` — advance the theory to
     the `by aoa` line so the lemma is the live proof goal.
   - if `--sh-timeout` is set, `repl.config(['auto_sledgehammer_params = "timeout = N"'])`.
   - `run_app('Minilang.AoA')` hands the socket to the ML app, then
     `_write((invocation_id, "test.<name>", (cfg, budget), None, None, None))`.
   - read back `(status, elapsed, cpu_time, detail, cost)`.

The driver slot is `f"{mode}.{name}"` = `"test.<name>"`. On the Python side `IsaMini_AoA`
(`toplevel.py`) splits it into `("test", name)`, looks up the `_test_driver` sentinel registered at
`Session.Driver["test"]`, and calls `TESTS[name].run(connection, log_dir, global_context, ptree)`.
`global_context` (a `Context`) and `ptree` (the `(Goal|None, int)`) come from the live `by aoa`
sequent the ML side captured via `Proof.refine_primitive`.

> **The case is selected by `name`, via the `"test.<name>"` driver string the runner sends — NOT by
> the `declare [[AoA_driver=…]]` inside the `.thy`.** Existing fixtures carry stale/mismatched
> declares (e.g. `Test_Have1.thy` declares `test.ProveInTime_ParseError` while the test is `Have1`);
> in test mode that line is ignored.

### 9.2 What `ModelTestCase.run` does

- Deletes any stale `Tests/<name>.diff` / `<name>.actual.yml` up front.
- Builds `Session` + `Root((global_context, ptree), connection)`, `await session.initialize(root)`.
- Runs the test op: `result = self.opr(root, MyIO(buffer))`; `if inspect.iscoroutine(result): await
  result`. Everything the op writes to the `MyIO` is captured in `buffer`.
- Compares `buffer` to `Tests/<name>.yml` (`correct_yaml_path`):
  - exists & differs → `save_diff` writes `<name>.actual.yml` + `diff -u` into `<name>.diff`, then
    `raise TestFailed(...)`.
  - does not exist → `write_expected_yaml` creates the golden (a brand-new test "passes" trivially —
    inspect the generated golden before trusting it).

`TestCase` is an ABC; `ModelTestCase` is the only concrete subclass, and `@model_test` is the only
registrar.

### 9.3 Authoring a case

```python
@model_test("Have1", "Test_Have1.thy", 9)   # name = golden stem; file = .thy fixture; line = the `by aoa` line
async def _test_Have1(root: Root, file: MyIO):
    print_header("Initial", file); root.print(0, file)     # dump fresh tree into the diff buffer
    root.session.age += 1                                   # bump render generation between edits
    await root.fill("1", [Have.gen_single({
        "thought": "helper",
        "statement": {"english": "...", "conclusion": r"(0::int) \<le> x * x"},
        "name": "lem1"})])
    print_header("After Have", file); root.print(0, file)
    root.session.age += 1
    await root.fill("1.1", [Obvious.gen_single({"facts": []})])
```

- **`.thy` fixture** (in `contrib/Isa-Mini/IsaMini/AoA/Tests/`) — minimal: `imports
  Minilang_AoA.Minilang_AoA`, the lemma, and `by aoa` at `line`. The lemma's goal becomes the
  `root`'s initial pending goal (one `GoalNode` per subgoal). Each test needs its **own dedicated
  `.thy`** (the `line` pins exactly one `by aoa`).
- **Edit API** (all `async`, return an `EditOutcome`, never raise — a bad id lands in `.failure`):
  `root.fill(id, [op,…])`, `node.append([op,…])`, `root.insert_before(id, …)`, `root.delete([id,…])`,
  `root.amend(id, …)`. Unpack the result with `[n] = (await …).committed`. Node ids are dotted paths:
  `"1"`, `"1.1"`, `"global.1"`; `Branch`/`CaseSplit` use **named** children — `"1.0.1"` is the
  exhaustiveness obligation, `"1.True.1"` / `"1.Nil.1"` are the cases.
- **Operations** via `Cls.gen_single(ToolArg)` → a `Parsed_Opr` (validates the dict). Common shapes:
  - `Have`: `{thought, statement: {english, conclusion, for_any?: [{name, type}], premises?:
    [{name, term}]}, name}`
  - `Obvious` (= Sledgehammer leaf): `{facts: [{name}]}`
  - `Branch`: `{thought, cases: [{statement: {english, isabelle, name}}]}`
  - `InferenceRule`: `{thought, rule: None | {name}}`
  - `Obtain`: `{thought, variables: [{name, type}], constraints: [{name, isabelle, english}]}`
- **Emit output** for the golden with `root.print(0, file)`, `root.quickview(0, file)`,
  `print_header(msg, file)`, or plain `file.write(...)`. For **worker scoped views**:
  `session = root.session; session.role = model.Role_Worker(target=have_node)` then
  `session.print_proof_scope(0, file)`; restore with `session.role = model.Role_Major()`.
- To assert completion, render the count — `s = set(); root.unfinished_nodes(s); file.write(f"…
  {len(s)}\n")`. **Never** assert on `node.status` (§2).
- **`session.age += 1` between edits**: rendering is age-aware (it diffs against the previous render
  generation to decide what detail to reprint), mirroring the live agent's per-tool-call generations.
  Omit it only to deliberately exercise the no-bump render path.

### 9.4 Result classification & `remote_error`

`run_all_tests` counts `success` / `stuck` / `false_statement` / `resource_exhausted` as **pass**
(the latter three are legitimate expected-outcome assertions), and **everything else as fail**. A
`REPLFail` from the transport is printed as an error and skipped.

**`remote_error` ALWAYS means a golden-YAML diff mismatch — never an RPC fault.** Mechanism: a
mismatch raises the Python `TestFailed` inside `ModelTestCase.run`, which is running as an RPC callback
from ML; the exception crosses the bridge as `Remote_Procedure_Calling.Remote_Calling_Failure`, and the
`AoA_REPL_App` wrapper emits it on the normal output channel as status `"remote_error"` (so the client
reads it as a value, not a `REPLFail`). In test mode no LLM/tool/network code runs, so a `TestFailed`
is the only Python exception that can escape — hence `remote_error` ⇔ "golden differed". The actual
unified diff is on disk at `Tests/<name>.diff` (and `<name>.actual.yml`).

### 9.5 CLI

- `--repl-addr` (default `127.0.0.1:6666`) → `Client(repl_addr, 'HOL')`.
- `-f` / `--filter`: substring match on the test name; accepts `,` or `|` as OR separators.
- `-x` / `--exclude`: comma-separated substrings; a test is dropped if any matches.
- `--sh-timeout N` (default 10): per-case Sledgehammer timeout; affects tests that actually hammer.

### Hard rules

- **Never modify, regenerate, overwrite, or delete a golden YAML
  (`contrib/Isa-Mini/IsaMini/AoA/Tests/*.yml`) without the maintainer's explicit approval — no
  exceptions.** This holds even when you are certain the new output is correct: a test going green
  again is not authorization. Surface the generated `.diff` / `.actual.yml`, explain why the golden
  should change, and wait for approval before touching any `Tests/*.yml`.
- **Each `@model_test` needs its own dedicated `.thy`** — never shared.
- `contrib/Isa-Mini/test_AoA.py` output is huge — always redirect to a file
  (`python contrib/Isa-Mini/test_AoA.py -f NAME > /tmp/aoa.txt 2>&1`).
- **Never run `contrib/Isa-Mini/test_AoA.py` in parallel or in the background** — one at a time,
  foreground only.
- **Shared working directory:** never `git stash` / `checkout` / `reset --hard` / `add` — multiple
  agents run concurrently here.
- **Never send raw bytes to the REPL on `6666`** to probe it — check liveness with
  `ss -tlnp | grep 6666` or `lsof`.

---

## 10. Conventions & gotchas

- **Status:** a node's `status` is the status of its *own* operation (a leaf op, or a block's
  *beginning* op) — never of its subtree. "Is the (sub)tree proved?" is **always**
  `is_proof_finished()` / `unfinished_nodes` empty (§2). This is the recurring bug.
- **Terms:** agent-facing text uses `IsaTerm.unicode` (or `MiniLang_Agent.string_of_*` on the ML
  side); RPC uses `.ascii`. Never `str()` an `IsaTerm` — raw `Syntax.*` output leaks PIDE markup.
- **Async / contextvars:** the ambient session is `_session_var` (`the_session()`). Forks and workers
  must launch in a *fresh* copied context — `_make_fork` raises `InternalError` if `_session_var` is
  still set.
- **ML side:** load the `isabelle-ML` skill before editing any `.ML`. The agent's operations
  ultimately drive `library/proof.ML`; AoA-specific wiring is `Agent/agent_server.ML` and
  `Agent/Minilang_AoA.thy`.
- **Logging:** per invocation under `<AoA_log_dir>/<invocation_id>/` — `interaction.yaml`,
  `proofs.yaml`, `proof_oprs.yaml`, `meta.jsonl.zst`, `proof.json`.
- **User-facing wording** (prompts, warnings, error text): propose scaffolding, let the maintainer
  pick the wording — don't author it autonomously.

---

## 11. File map

| File | Role |
|---|---|
| `model.py` | Proof tree, nodes, `Minilang_State`, `Session`/`Role`, rendering — the core. |
| `toplevel.py` | RPC entry `IsaMini.AoA`, caching, test dispatch. |
| `mcp_http_server.py` | MCP server + tool→operation logic + `ToolExecutor`. |
| `language_model_driver.py` | Driver base, retry logic, `WorkerHandle`/worker events. |
| `driver_claude_code.py` | Default driver (Claude Agent SDK over HTTP MCP). |
| `driver_api.py` and `driver_{openai,anthropic,gemini,codex}.py` | Provider/driver variants. |
| `prompts.py`, `retrieval.py`, `proof_cache.py`, `tools/*.jsonc` | Prompts, semantic retrieval, cache, tool schemas. |
| `test.py`, `Tests/*`, and the runner `../../test_AoA.py` | Test framework + golden YAMLs + `.thy` fixtures. |
| `../../Agent/agent_server.ML`, `../../Agent/Minilang_AoA.thy`, `../../library/proof.ML` | ML side. |
