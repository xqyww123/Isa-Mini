# AoA (All over Abstraction) — Developer Guide

AoA is the AI-agent framework that drives Isabelle proofs through the Minilang proof language. An agent (planner) builds a proof tree of high-level operations; sub-agents (workers) discharge individual lemmas. This document is the reference for working *on* AoA itself.

> References below use stable symbol names (`Class.method`), never line numbers — line numbers drift. Grep for the symbol.

**ML side:** `../../Agent/` (`agent_server.ML`, `Minilang_Agent.thy`) and `../../library/proof.ML`
**Note:** The live agent code is this directory — NOT the stray top-level `../../IsaMini_AoA/` (which holds only a leftover `driver_codex.py`). For the broader Minilang project layout see the `isa-mini` skill.

Always also load the `isabelle-ML` skill before touching any `.ML` file (per project memory).

---

## ⚠️ #1 GOTCHA: a node's `status` is NOT its subtree's proof status

The most common mistake. `node.status.status` reports only the node's **own operation**; "is the subtree proved?" is a **separate** question with a separate test.

**What `status == SUCCESS` means — depends on the node type:**

- **`Leaf`** (`Obvious`, `Rewrite`, `Intro`, …): the leaf's operation ran without error. For `Obvious` (= Sledgehammer) this *does* mean the goal was closed — a failed hammer raises `IsabelleError` → FAILURE (and that failure is what triggers worker dispatch). This coincidence is what makes the trap easy to fall into.
- **`StdBlock`** (`Have`, `Obtain`, …): **only the block's beginning operation** opened cleanly — never the body. For `Have`, that means the statement is well-formed and the subgoal was opened; it says **nothing** about whether the body proves it. A `Have` with an empty/open proof is still SUCCESS, because `NonLeaf_Node._refresh_me_alone`'s `head_succeeded` branch calls `_skip_proof` → `sorry_end_all` to cheat the leftover goal and then records SUCCESS.

**To test whether a (sub)tree is actually proved — always use `is_proof_finished()` / `unfinished_nodes()`, never `status`:**

```python
def is_proof_finished(self) -> bool:
    s = set(); self.unfinished_nodes(s); return len(s) == 0
```

`NonLeaf_Node.unfinished_nodes` flags a node — **even a SUCCESS one** — when it is still `opening()` (`_closed_by is None`) **and** `has_pending_goal()` (its `_state_before_ending_` has a real `leading_goal` ≠ placeholder `True`). For a block, `status == SUCCESS` (beginning op opened) and `is_proof_finished()` (whole subtree discharged) are therefore **orthogonal**.

The other two status values (`EvaluationStatus.Status`): **`FAILURE`** = the node's own operation errored (a leaf op, or a block's beginning op — e.g. an ill-typed statement). **`CANCELLED`** ("pending" in display) = never evaluated, because an earlier sibling failed (set by `Node._cancel`). A fresh node starts at `EVALUATION_NOT_YET`, a FAILURE. (`_changes_pending_goal` is declared but never read — ignore it.)

### Why declarative nodes expose facts before being proved

`_is_declarative` nodes (`Have`, `Obtain`, `Define`, …) make their named fact available to later steps regardless of proof status — mirroring Isar `have name: P sorry` keeping `name` usable. `Have._fixed_facts_after_me` unconditionally adds `name : conclusion` to successors' hypotheses, with no status guard. This is *why* `Session.print_proof_scope`'s "available declarations" filter deliberately includes posed-but-unproved SUCCESS declarations — they are genuinely in scope.

---

## Three different "state/session" concepts — don't conflate them

| Concept | What it is | Cardinality |
|---|---|---|
| **Isabelle / REPL session** | One Isabelle process behind the `Connection` (Isa-REPL server, default `127.0.0.1:6666`) | **1** per `by aoa` |
| **`Minilang_State`** | A *named* server-side proof-state snapshot (`name` like `$init`/`$1`) + the shared `connection`; holds `leading_goal`. Ops run via `connection.callback("IsaMini.proof_opr", (from, to, (cmd,arg)))` in `Minilang_State.execute` | **many** (per node before/after states) |
| **Python `Session`** | An *agent context* (planner, worker, or interaction fork). Forks share the same `Connection`, `Root`, and `Runtime` | **many** (planner + forks) |

The Python `Session` is **not** an Isabelle session. Workers do not open a new Isabelle session or a new proof tree — the driver's `_make_fork` sets the child's `root = parent.root`; `Runtime` is the singleton shared across all Sessions on one proof tree.

---

## Architecture map

### Entry / RPC wiring
- User writes `by aoa` → method registered by `method_setup aoa` in `../../Agent/Minilang_Agent.thy`; method body is `MiniLang_Agent_AoA.method` in `../../Agent/agent_server.ML`. Default driver `"ClaudeCode"` (config `agent_AoA_driver`).
- AoA is **one long-lived RPC command** `IsaMini.AoA` (ML builds `aoa_cmd` in `agent_server.ML`; Python handler `IsaMini_AoA`, decorated `@isabelle_remote_procedure("IsaMini.AoA")` in `toplevel.py`). Inside it, **Python calls back into ML** repeatedly (`IsaMini.proof_opr`, `reset_state`, `lookup_fact`, `check_term`, …; ML callbacks defined in `agent_server.ML`).
- Registered as the Isa-REPL app `Minilang.AoA` (`REPL_Server.register_app` in `agent_server.ML`). Clients connect, advance to the `by aoa` line, `run_app('Minilang.AoA')`.
- Caching (in `IsaMini_AoA`): Python SQLite (`proof_cache.py`) → ML Phi_Cache JSON → full run. Hits replay packed ops via `set_replay_mode` + `proof_opr` (`_replay_cached_proof`).

### Core data model (`model.py`)
- **`IsaTerm`**: dual `.unicode` (agent-facing) / `.ascii` (RPC). `str()` is **forbidden** (raises). Build via `IsaTerm.from_isabelle(ascii)` / `IsaTerm.from_agent(unicode)`.
- **`Context` = (vars, tvars, hyps)`, `Goal` = (context, conclusion)`, `Goals`**.
- **Node hierarchy** (a diagram lives as a comment near the top-level node classes in `model.py`):
  - `Node` (ABC) → `Leaf` (single op) / `NonLeaf_Node` (has `sub_nodes`, `_closed_by`).
  - `StdBlock(NonLeaf_Node)`: `beginning_opr` / `ending_opr` (default `END`) / `_state_before_ending_`.
  - `GoalContainer` (children are independent subgoals; emits `NEXT`), `GoalNode(StdBlock)` (one subgoal's steps), `SubgoalMaker(GoalContainer, StdBlock)` (opens N child `GoalNode`s).
  - `GlobalEnv(StdBlock)` (id `"global"`, only `_is_declarative` children), `Root(GoalContainer, StdBlock)` (`sub_nodes[0]` = GlobalEnv, `sub_nodes[1..]` = top-level GoalNodes). Node ids look like `"global.1"`, `"2.1"`.
  - Proof ops (each registered via `@proof_operation`): `Have`, `Obtain`, `Suffices`, `Intro`, `InferenceRule`, `SplitConjs`, `Branch`, `CaseSplit` / `Induction` (both `CaseSplit_Like`), `Define`, `Obvious` (→ `HAMMER`), `Witness`, `Compute`, `Unfold`, `Derive`, `Rewrite`, `SetupRewriting`, `Chaining`, `Contradiction`.
  - These compile to `Minilang_Operation` factory methods: `HAVE`, `OBTAIN`, `RULE`, `HAMMER`, `INTRO`, `SUFFICES`, `BRANCH`, `CASE_SPLIT`, `INDUCT`, `END`, `NEXT`, `SORRY_*`, ….

### Session / Roles / workers
- **Role ADT**: `Role_Plan(stage ∈ {PLANNING, FINISHING})`, `Role_Worker(target, suggestions, useful_lemmas, worker_handle)`, `Role_Interaction(...)`. Predicates `Session.is_major` / `is_planning` / `is_worker` / `is_interaction`.
- **`Runtime`**: shared singleton — `age`, depth limit (30), `total_tool_calls`, `worker_max_tool_calls` (500).
- **Worker dispatch**: planner builds structure → `Session.complete_proof` switches to FINISHING, re-evaluates, collects failed `Obvious` parents (`_collect_failed_obvious_parents`), dispatches a Worker per target via `Interaction_ChooseTarget` + `fork_interaction`. `WorkerHandle` (in `language_model_driver.py`) owns the worker task + event queue (`WorkerRefute` / `WorkerRequestLemmas` / `WorkerDifficulty` / `WorkerSurrender` / `WorkerDone`). A lemma sub-agent (spawned when the planner accepts a worker's `request_lemmas`) is a first-class `WorkerHandle` driven by a `LemmaDrive` targeting a `Have`. Worker success = `target.is_proof_finished()` (NOT status!).
- **Worker scoped view**: `Session.print_proof_scope` — a non-worker prints the whole `root`; a worker prints root context (`variables:` / `premises:` from `root.context`), an `available declarations:` section (preceding *declarative SUCCESS* siblings in `global_env`, see the §1 gotcha), the target goal, and the target's own substeps. `Session.quickview_proof_scope` is the compressed analogue.

### Drivers
- Base `LMDriver(Session)` (`language_model_driver.py`): `run()` dispatches by role; retry layers `_with_retry` (quota, 20-min wait) + `_retry_transient` (1.5ⁿ backoff).
- `driver_claude_code.py` — **default** (`ClaudeCode`); uses the Claude Agent SDK pointed at the singleton HTTP MCP server (`mcp_servers={"proof": {type: http, url}}`).
- `driver_api.py` — `APIDriver`: owns its own chat loop, calls `Provider.chat()`, executes tools via in-process `ToolExecutor`, compacts at ~80% context.
- `driver_openai.py` / `driver_anthropic.py` / `driver_gemini.py` / `driver_codex.py` — provider variants (lazy-imported in `toplevel.py`).
- **Tools** (abstract ids in `model.py`): `edit` (TOOL_EDIT), `delete`, `query` (TOOL_SEARCH), `recall` (TOOL_READ), `report` (worker→dispatcher: refute / surrender / difficulty), `request_lemmas` (dual-role: worker→planner channel, or planner self-formalize hint), answer-*. Tool→op mapping in `mcp_http_server.py` (`_edit_tool_logic` → `root.fill` / `insert_before` / `amend`; `_delete_tool_logic` → `root.delete`). Schemas are JSONC in `tools/`.
- **MCP server** (`ProofMCPHTTPServer` in `mcp_http_server.py`): singleton multi-session HTTP server, per-session endpoints `/mcp/<session_id>` (`_SessionRouter`); `call_tool` sets `_session_var`, permission-checks (`_check_tool_permission`), delegates to a per-session `ToolExecutor`.

### Rendering
- `print` (full, `Root.print` / `Node.print`) vs `quickview` (compressed, `Node.quickview`; runs of ≥5 unchanged children collapse via `_quickview_children_compressed`).
- Helpers in `model.py`: `print_vars` (banner `variables`), `print_hyps` (banner **`premises`**), `print_goal`, `print_pending_goal` (banner **`pending proof goal:`**). Worker view adds banner **`available declarations:`** (in `print_proof_scope`).
- Agents read/write `proof.yaml` — written on init, rewritten by `Session.refresh_YAML` via `print_proof_scope`; the `recall` tool reads it.

---

## Test framework

`test.py` (this directory) holds the cases; `../../test_AoA.py` is the runner. A test drives the proof tree **by hand** (no LLM, no tool calls) and diffs the rendered output against a golden YAML. So these are deterministic snapshot tests of the model + renderer.

### How a run works
> The case is selected by `name` via the `"test.<name>"` driver string the runner sends — **NOT** the `declare [[agent_AoA_driver=…]]` inside the `.thy` (existing fixtures carry stale/mismatched declares; in test mode they're ignored). One long-lived Isabelle session for the whole run; per-case isolation is a `rollback` to a recorded clean state, not a restart.

### Authoring a case
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
- Each test needs its **own dedicated `.thy`** — the `line` pins exactly one `by aoa`. The `.thy` just states the lemma (its goal becomes the `root`'s initial goal).
- **Edit API** (all `async`): `root.fill(id, [op,…])`, `node.append([op,…])`, `root.insert_before(id,…)`, `root.delete([id,…])`, `root.amend(id,…)`. They return an `EditOutcome` (never raise — a bad id lands in `.failure`); unpack with `[n] = (await …).committed`. Node ids are dotted: `"1"`, `"1.1"`, `"global.1"`; `Branch`/`CaseSplit` use **named** children (`"1.0.1"` = exhaustiveness obligation, `"1.True.1"`, `"1.Nil.1"`).
- **Operations** via `Cls.gen_single(ToolArg)` → a `Parsed_Opr`. Common ToolArg shapes (copy from existing tests): `Have` `{thought, statement:{english, conclusion, for_any?:[{name,type}], premises?:[{name,term}]}, name}`; `Obvious` `{facts:[{name}]}`; `Branch` `{thought, cases:[{statement:{english,isabelle,name}}]}`; `InferenceRule` `{thought, rule: None | {name}}`; `Obtain` `{thought, variables:[{name,type}], constraints:[{name,isabelle,english}]}`.
- **Dump state** for the golden: `root.print(0,file)`, `root.quickview(0,file)`, `print_header(msg,file)`, or `file.write(...)`. For **worker scoped views**: `session = root.session; session.role = model.Role_Worker(target=have_node)` then `session.print_proof_scope(0,file)`; restore with `session.role = model.Role_Plan()`.
- To assert proof completion, render the count: `s=set(); root.unfinished_nodes(s); file.write(f"unfinished: {len(s)}\n")` — never check `status` (the §1 gotcha).
- `session.age += 1` between edits: rendering is age-aware (diffs against the previous render to decide what detail to reprint), mirroring the live agent's per-tool-call generations. Omit it only when deliberately exercising the no-bump render path.

### Run & interpret
- `python ../../test_AoA.py -f NAME` (`-x EXCL`, `--sh-timeout N`, `--repl-addr`). `-f`/`-x` are **substring** matches on the test name (`-f` accepts `,` or `|` as OR separators; `-x` is comma-separated). **Always redirect** (`> /tmp/aoa.txt 2>&1`) — output is huge — and run one at a time, foreground only.
- Status classification in `run_all_tests`: `success` / `stuck` / `false_statement` / `resource_exhausted` → **pass**; anything else → **fail**.
- **`remote_error` ALWAYS means a golden-YAML diff mismatch** — a `TestFailed` from `ModelTestCase.run` surfacing across the RPC bridge as `Remote_Calling_Failure`, NOT an RPC fault. The real diff is on disk: `Tests/<name>.diff` and `<name>.actual.yml` (both auto-cleaned at the start of the next run of that case).

### Hard rules (from project memory / repo CLAUDE.md)
- **NEVER modify, regenerate, overwrite, or delete a golden YAML (`Tests/*.yml`) without explicit user approval — no exceptions.** This holds even when you are certain the new output is correct: the test passing again is not authorization. Surface the `.diff`, explain why the golden should change, and wait for the user to approve before touching any `Tests/*.yml`.
- **NEVER share a `.thy` file** between two `@model_test`s — each needs its own.
- `../../test_AoA.py` output is **huge** → always redirect to a file (`> /tmp/aoa_test.txt 2>&1`).
- **Never run `../../test_AoA.py` in parallel or in the background** — one at a time, foreground only.
- **Shared working dir:** never `git stash` / `checkout` / `reset --hard` / `add` — other agents run concurrently.
- **Never send raw data to the REPL on 6666** — to check liveness use `ss -tlnp | grep 6666` or `lsof`.
- **User-facing text** (prompts/warnings/errors): never author wording autonomously — propose scaffolding and let the user pick (memory).

---

## Development checklist
1. "Is this (sub)tree proved?" → **always** `is_proof_finished()` / `unfinished_nodes()` empty. A node's `status` is only its *own* op's status (leaf op, or a block's *beginning* op), never its subtree's — don't use it to judge completion (the §1 gotcha).
2. Editing `.ML`? Load `isabelle-ML` first.
3. Agent-facing text uses `IsaTerm.unicode` / `MiniLang_Agent.string_of_*`; RPC uses `.ascii`. Never `str()` an `IsaTerm`.
4. New rendering/behavior changes golden YAMLs → run the affected test, review the `.diff`, and **get explicit user approval before updating any golden** (never update them on your own — see Hard rules).
5. Forks/workers must launch in a fresh contextvars context (`_make_fork` raises if `_session_var` is set).
6. Logs land in `<AoA_log_dir>/<invocation_id>/`: `interaction.yaml`, `proofs.yaml`, `proof_oprs.yaml`, `meta.jsonl.zst`, `proof.json`.

## Key files
- `model.py` — proof tree, nodes, `Session`/`Role`, `Minilang_State`, rendering (the bulk).
- `toplevel.py` — RPC entry `IsaMini.AoA`, caching, test dispatch.
- `mcp_http_server.py` — MCP server + tool→operation logic.
- `language_model_driver.py` — driver base + worker plumbing.
- `driver_*.py` — concrete drivers (`driver_claude_code.py` is default).
- `test.py` / `Tests/*` (this directory) + the runner `../../test_AoA.py` — test framework + goldens.
- `../../Agent/agent_server.ML`, `../../Agent/Minilang_Agent.thy`, `../../library/proof.ML` — ML side.
- `docs/DEVELOP.md` — the longer-form design document (same material, with rationale).
