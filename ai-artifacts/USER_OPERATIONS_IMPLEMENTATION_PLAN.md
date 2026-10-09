# Implementation plan: user-defined proof operations and tasks

Written 2026-10-08 for implementation after a context reset. It is
self-contained: everything an implementer must know that is not in the
spec or in the code is here.

## 0. Status ledger

| step | state | notes |
| --- | --- | --- |
| 1 Isabelle_RPC `mk_callback` | done 2026-10-08 | `Tools/RPC.ML` re-raises whatever escapes the read; new `test/Test_Callback_Argument.thy`, registered in `ROOT`. Passed through the REPL (`ai-artifacts/probes/run_theory.py`); mutation-checked: with the old arm restored the same test fails with `Invalid response, protocol error`. Review round 1: `ends_with_error` matches `Exn.Exn (ERROR _)` exactly, no longer any exception. Round 2 (F6, per case, each with the old arm restored through a REPL restart): the integer case fails first in the whole theory; the string case alone fails with "not the reader's error: Remote_Calling_Failure … Traceback", Python's traceback as the remote error, as the header now says (A30). Round 3 (R1-1, R1-3): `Inner_Syntax_Error.decode` makes decoding an error message total (a message that is not well-formed YXML decodes to its plain text), used by `parse_offsets` and `clean_prose`; `clean_prose` is no longer exported. Mutant killed: the guard removed, yxml.ML's Fail escaping into the Interpret test's chr 5 / chr 6 case. The owner deleted `BUG_CALLBACK_UNPACK_DESYNC.md`; TAT_Framework.ML:927's "must not raise" comment is told to the TAT sessions with the Step 6 notice (owner agreed). Uncommitted, in the Isabelle_RPC submodule. |
| 2 one BinIO codec, in-memory streams | done 2026-10-08 | `agent_packer.ML`: functor, twins and the D31 note gone; `instream_of_bytes`, `bytes_of_output` exported; after review round 1 `bytes_of_output` opens with `IO.BLOCK_BUF` and closes the stream in a `\<^try>…finally`. `agent_server.ML`: both blob sites use them, through `encode_blob`/`decode_blob` defined before `raw_AoA`. `Test/Test_Agent_Packer_Recorded_Proof.thy`: on the BinIO codec, plus test 4 decoding a blob from `Tests/Test_Branch.proof-store` (legacy single-time HAMMER slots, so no byte-identical re-encode; the decoded shape is checked). Passed: that theory, `Test/Test_Proof_Store_Hash_Hit.thy`, `test_AoA.py -f Branch1`. The owner was told D31 is retired. The REPL is started by me: `isabelle REPL -l Minilang -o threads=12 -T 1800 127.0.0.1:6666 /home/qiyuan/Current/MLML/cache/repl_tmps/aoa_user_ops_6666` (Isabelle_RPC, Semantic_Embedding and Minilang_AoA load from source; ~20 s). Stop it by killing its `bin/java` process (never jEdit's, pid 1181664) and the poly children. |
| 3 `agent_config.ML`, `agent_plugin.ML` | done 2026-10-08 | New files as spec §1; `agent.ML` re-exports the config types; load order in `Minilang_AoA.thy`. Order: name order (`sort_by`, i.e. `string_ord`, not the table's `fast_string_ord`), the owner's final decision in review round 2 (OQ4, after round 1's Q9 had made it registration order, whose serials turned out to depend on the scheduler between independent plugin theories); the serial an entry carries serves the merge alone. `lookup_operation`/`lookup_task` became `the_operation`/`the_task`, raising the approved text on a miss (Q1 (b)); round 2 (A28) wrote the insert, merge and lookup rules once as helpers, each label bound once. Test `Tests/User_Operation_Registry_Test.thy` (`theory_test "UserOperationRegistry_Minilang"`), green through the REPL; round 2 gave it real diamond merges for both registries (A5), with names whose table order differs from name order. Mutants killed: seven in round 1; in round 2 `Symtab.merge (K false)` and `(K true)` for each registry, four. Texts: `User operation "X" is registered twice` / `User task "X" is registered twice` (approved 2026-10-08), `User operation "X": no imported theory registers it` (reused approved codec text). |
| 4 the `USER` command, `derived_subgoals_of` | done 2026-10-08 | `USER` in both datatype copies; `reject_shared_schematics` + the `USER` branch of `interpret_i`; `read_method_text` used by `try_cached_apply` and `exec_split_script`; signature exports `read_method_text`, `check_authored_props`, `check_authored_terms`. `proof.ML`: new contract (shrink → `[]`; grew → first `Goals` else the new frame's goals; a solved sequent derives none — `goals_of'` spells it `[True]`, which the agent must not see). Test `Tests/User_Operation_Interpret_Test.thy` (`theory_test "UserOperationInterpret_Minilang"`, eleven cases incl. a HAVE-composing opener, an END-composing closer, two conjI steps on `(A ∧ B) ∧ C`, the named BRANCH opener on a plain and on a schematic goal, and the reader's failures compared exactly — review round 2, A3/A14/A15), green through the REPL; the 14 gate/probe model tests (CaseSplit, PostInstRule*, GateSchematic, InferenceRule*, IntroSplitConj, Branch1) still green. An unregistered name reached at execution raises `the_operation`'s ERROR (the approved codec text; there is no INVALID_OPR text). Round 2 (A1) rebuilt `read_method_text`: the plain read gives the value, a positioned re-read of the same text only marks a failure, `Undefined tactic` is built from the name the agent wrote, and a text that does not tokenize reads `Outer syntax error: <marked>` (OQ1); `mark_window` accepts the end of the text (A26). Mutants killed: five in round 1; in round 2 the run's messages dropped, the first `Goals` dropped, the first `Goals` forwarded in place of the state, the marker without a window, the lexical handler removed, Isabelle's `check_text` in place of the name-based text — six. Round 3 (R1-2, R4-1, R4-2, R4-6, R4-7): the reader's failure functions became one `located` and `fail prefix`, the probe through `Exn.result`; case 11 compares every text exactly, with a chr 5 / chr 6 text (unmarked), a failure near the end, at the end, and two in the middle of a long text (both ellipses; the syntax-error path and the leftover path), each window computed by `mark_window`'s rule by hand and confirmed in the run; `refused` goes through `Exn.result`; the vacuous "the block is open" assertion is gone; the `argument` helper lives in the test base. |
| 5 the codec's `USER` branch | done 2026-10-08 | `xcmd_packer`/`xcmd_unpacker` take the theory; the five users in `agent_server.ML` pass it (`thy` bound in `raw_AoA`; `aoa_replay_method` uses its `ctxt`); the recorded-proof test passes `\<^theory>`. Test `Tests/User_Operation_Codec_Test.thy` (`theory_test "UserOperationCodec_Minilang"`), green through the REPL; two mutants killed. Probe for ML-only work: `<scratchpad>/run_ml_blocks.ML` under `isabelle ML_process -l Minilang_AoA` (re-evaluates `proof.ML` and the agent chain in a probe theory, then every `ML` block of the given test theories); the `Minilang_AoA` heap must be fresh enough to load — the REPL tool rebuilds it when started with `-l Minilang_AoA` (done once on port 6667, then killed). |
| 6 `agent_server.ML`: entry points, call start, messages, callers | done 2026-10-08 (ML side; the Python unpacking of the 12th field is in `toplevel.py` already) | `usual`/`learning` values; `raw_AoA`/`run_AoA`/`hammer_or_AoA` take `task` and `user_operations`; start of the call (`active_operations`, `the_task`, one `load` of `IsaMini.AoA` plus the packages, `current_config`, `env`, the user callbacks with the one name check, the names as the 12th field of the `IsaMini.AoA` argument via `packTuple12`); `minilang_message_packer ctxt running_op` with `pack_opt` and tag 21; callers: `aoa_repl_app.ML`, test 24, `tasks/AoA-learning/learning.ML`, phi-system `reasoners.ML` (submodule). The TAT jobs session [9ffa3c] was notified (signature + the obsolete "must not raise" comment); the compile session [ebfd21] no longer exists. Every `USER` command from the wire or a stored blob passes the codec, whose `the_operation` raises for an unregistered name first, so `interpret_i`'s own arm for that case fires only for a `USER` value built in ML (the interpret test exercises it that way). The TAT jobs session's two add-only changes in this file and `proof_store_AoA.ML` (`hammer_or_AoA'` returning the stored times beside the text, `replay_record` hoisted and exported; CONSTRUCT_DECISIONS §15) sit on top of this step's fields and ride in the same commit, named in its message. Checked through the REPL: Branch1, every `Induction*` test, the three theory tests, `Test_Proof_Store_Hash_Hit.thy`, `Test_Agent_Packer_Recorded_Proof.thy`. Round 2: `running_op` by the lookup `interpret_i` makes (A22); the blob-codec comments name `encode_blob`/`decode_blob` (A20, also `preprocess.ML`); the implementation comment back above `fun raw_AoA`, pointing at the signature comment (A21). `Tests/User_Operation_Call_Test.thy` checks seven refusals (ML-CALL-3); round-2 mutants killed: the clash check's first disjunct, its accumulation, the toplevel task guard. Texts (approved 2026-10-08): `User task "X": no imported theory registers it`; `Callback "x" of a user operation: the name is already taken`. |
| 7 Python model | done 2026-10-08 (REPL check of the model tests pending with Step 8's) | `edit_schema.py` (new: `load_schema`, `BASE_EDIT_SCHEMA`); `task.py`: `TASK_REGISTRY`, `@aoa_task` (duplicate/abstract checks), `usual`/`learning` registered, `UsualTask(payload)`; `model.py`: `_refuse_schematic_goal` (Branch calls it), `UserNode` (schema checks in `_check_registration`, `the_operation`/`beginning_opr`, gate, the Leaf rule), `@proof_operation` checks, `unpack_message(data, user_cls)` + tag 21 in `Minilang_State.execute`, `Runtime(user_operations)` building the call's table with its two refusals, `Session.operations`, `Parse_Nodes` on the table, `ArgumentError_UnknownProofOperation(arg, operations)`, the `SubgoalMaker` default `_ending_opr_err_msgs` (five copies gone: SplitConjs, InferenceRule, Branch, CaseSplit, Induction). Deviation from the spec's file table: the task registry lives in `task.py` (model.py imports task.py; the reverse would be circular). Round 2: `BUILTIN_OPERATIONS` with its import-time check against the base schema's `Operation.anyOf` (A9), since round 3 the function `_check_builtins_advertised`, tested (R3-4); `Task.__init__(payload)` on the base class, a generic `@aoa_task`, `runtime` on `SessionConstructor` (A16/A17); the shared helper is `check_name_and_abstractness` (A31). `test_user_operations.py`: 34 pytest cases green (24 at first, 29 after round 1, 32 after round 2, 34 after round 3); mutants killed: 13, then 6, then 4, then 4 (in memory, one per process); the script-style unit tests (`test_budget_exempt`, `test_corrupted_sample`, `test_deep_restart`, `test_session_quit`, run as scripts) and the pytest ones still pass. Texts (approved 2026-10-08) are in the code: decorator refusals, `Runtime`'s refusals, the Leaf rule, the tag-21 bug guard. |
| 8 Python call start and schemas | done 2026-10-08 (REPL check pending) | `toplevel.py` builds the `Runtime` (table + task from `TASK_REGISTRY`) right after unpacking, passes it to the drivers and to `TestCase.run`; `test.py` `Session(..., runtime=runtime)`; `mcp_http_server.py`: `_edit_schema_for`, `_tool_schemas_for` injects the call's `edit` schema, `_TOOL_SCHEMAS["edit"]` has no schema, module constants gone, `_assert_no_refs` runs inside the two derivations; `driver_openai_api.py`: `_strict_schema`s are pure functions, DeepSeek's sub-proof rule by the key names `proof`/`proofs` (Q4), since round 2 applied to property names only, with `minItems`/`maxItems`/`default` dropped as schema keywords only (A8); cache gone; `driver_gemini.py`, `driver_codex.py` likewise. The four derived forms of the base schema are byte-identical to the captured pre-change output (`<scratchpad>/before_*.json`). Tests in `test_user_operations.py` (schema of the call, every derived form, the providers' seams, each flattening's own `_assert_no_refs`, a plugin field named like a keyword); mutants killed: five in round 1; in round 2 each flattening's own check deleted (two), the table filled in the order the classes were registered in, the keyword-named field dropped again. Round 3 (R3-1, R3-3, R3-5): `_strictify_schema` walks a `properties` map as field names too, so a plugin field named `properties` keeps its schema and DeepSeek's and OpenAI's forms stay valid schemas (pinned with jsonschema's `check_schema`); the `simplify` hint has a test; the DeepSeek derivation says "field" throughout. Mutants killed: the map walked as a schema node again, the hint deleted. |
| 9 sample plugin and tests | done 2026-10-08 (goldens await the owner's approval) | `Tests/Sample_Plugin.thy` (ML: `Apply` with its own message `APPLIED`, `HaveText` composing HAVE, `TwoGoals` a Leaf leaving two, `Consider` composing BRANCH; all `default = true` because `by aoa` and the model-test path pass `[]`) and `Tests/sample_plugin/__init__.py` (the four node classes). Seven `@model_test`s with their own fixtures: `UserOp_Apply`, `UserOp_WithInduction`, `UserOp_ApplyShared` (refused with the approved text naming `?s`, then `trans[of a b c]`), `UserOp_HaveText`, `UserOp_HaveText_Schematic`, `UserOp_Consider` (gate), `UserOp_TwoGoals` (Leaf rule); two theory tests `User_Operation_Replay_Test.thy` (a blob of `USER` steps ending with `END []` replays; stale in a context without the plugin) and `User_Operation_Call_Test.thy` (call-start refusals). All 12 green through the REPL. Found and fixed on the way: a `StdBlock` plugin class's sub-proof is attached by `UserNode._refresh_the_beginning_opr` (each built-in block attaches its own; the first run's goldens showed `proof: empty`). The seven first goldens `Tests/UserOp_*.yml` were approved by the owner (three of them, `HaveText`, `HaveText_Schematic`, `ApplyShared`, regenerated after I deleted my own first-run outputs, which the owner was told). Review round 1 changed the sample (`Apply` bounded by `mini_single_cmd_timeout`, `TwoGoals` forwards no `Goals`, `Consider` with named cases and `_initial_goal_index = 0`), rewrote `UserOp_Consider` (the gate on a sibling schematic goal, `schematic_goal "PP 7 \<and> QQ ?y"`) and added `UserOp_ConsiderCases` (named cases on `(x::int) * x \<ge> 0`): eight model tests now; `UserOp_Consider.yml` regenerated and `UserOp_ConsiderCases.yml` new, both approved 2026-10-09 — the latter regenerated once more after its fill targets `1.first.1`/`1.second.1`, which `root.fill` refuses without raising, became `1.1.1`/`1.2.1`; `UserOp_TwoGoals.yml` byte-identical. Round 2 rewrote the replay test (A2/A6): the goal is the test base's `Opaque`, certified in the base theory itself, so the stale case differs from the positive one only in the plugin import; the `argument` helper asserts `pack_arg` inverts `unpack_arg`; three cases (a step, the stale replay, a block). Deviations from spec §9, now written into it: the "payload() mismatches unpack_arg" case is the codec theory test's hand-packed blob (plus the RPC test that a failing read ends the call); the block sample's sub-proof field is `proof`, per the Q4 convention, checked in pytest; the `pack_message`-without-decoder case is the pytest tag-21 default; the schema pytest uses `SampleLeaf`/`SampleBlock` in place of `Apply`. Round-2 mutants killed through the REPL: the HaveText unpack swap (the `argument` assert), the import-ignoring lookup (the stale case), the stream without its inner `END` (the block case), `whole=False` in the schematic gate (the pytest gate test and `UserOp_Consider`). Round 3 (R2-2, R4-4, R4-5): the registry test compares the approved texts exactly; the `argument` helper, with its inverse assertion, lives once in the test base; the two test.py comments name only each theory's subject. |
| 10 documents and notices | done 2026-10-08 | `docs/DEVELOP.md` (file-map rows + a paragraph pointing at the spec), `AGENTS.md`, `CLAUDE.md` (key-files rows), the spec (task registry in `task.py`; `UserNode` attaches the sub-proof). D31 told; TAT session told. The §4 texts are proposed to the owner in the final report. |

Update this table as steps land. "Done" means: edited, loaded without
error after a REPL restart (ML) or imported (Python), its tests green,
mutation-checked where the step adds a check.

## 1. What is being built, and where the truth is

A plugin system for AoA (the LLM proof agent of Isa-Mini): an Isabelle
theory registers user operations and tasks and names a Python package;
the package defines each operation's node class, JSON schema and
encoding. The spec is `IsaMini/AoA/docs/USER_OPERATIONS.md` (the owner's
decisions and two rounds of adversarial review are all folded in; it is
authoritative over this plan where they differ). Its running example is a
plugin `Apply` that applies a proof method given as text.

Settled facts that are easy to get wrong (all in the spec, repeated here
because they overturn earlier drafts):

- The argument of a user operation travels in place in the MessagePack
  stream (no bytes-in-bytes); the ML constructor is
  `USER of string * Universal.universal`; a plugin never sees `Universal`
  or an exception for its argument — `register_user_operation` is
  polymorphic (`'a user_operation`) and wraps with a `Universal.tag ()` of
  its own.
- `pack_message : exn -> MessagePackBinIO.Pack.raw_packer option` stays
  on `exn` (a plugin's messages are its own exceptions through
  `Minilang.Internal`); only the running operation's `pack_message` is
  asked; tag 21 carries the packing alone, `(21, p)`.
- One task shape, `type task = {name, payload}`, with `usual` and
  `learning` registered like user tasks; `pack_task` goes.
- Selection per call: `user_operations : (string * bool) list` beside
  `task` on `raw_AoA`, `run_AoA`, `hammer_or_AoA`; `by aoa` and
  `by hammer_or_aoa` pass `usual` and `[]` and expose no syntax.
- The shared-schematic-variable check runs in `interpret_i`'s `USER`
  branch for every user operation; `Goals` for a `USER` step is sent once
  by that branch from `derived_subgoals_of`; a `Leaf` derives at most one
  subgoal, checked in Python by `UserNode._execute_opr`.
- One codec over `MessagePackBinIO` serves the wire, the store and
  replay; the BytesIO functor goes.
- All plugins are trusted; checks exist to fail honest mistakes early.
- Agent-visible texts already approved are quoted verbatim in the spec
  (§2 the two codec errors, §4.1 the refusal and the `unpack_own_message`
  default). Texts not yet approved are listed in §4 of this plan and are
  proposed to the owner before they land.

Review artefacts (for the record, not needed to implement):
`/tmp/claude-1002/-home-qiyuan-Current-MLML/40a70c08-3f45-436f-b6c0-0134f71d31e7/scratchpad/verdict.json`,
`verdict2.json`, `verdict3.json` (the three judges' rulings).

## 2. Rules in force while implementing

- Never run `isabelle build` (no flags, no session). Allowed: the Isa-REPL
  server, `isabelle ML_process`, `isabelle scala_build`.
- After editing any `.ML` file, ask the owner to restart the REPL server
  before running tests; a running REPL keeps the old ML.
- Tests: `python -u test_AoA.py -f NAME > /tmp/aoa.txt 2>&1`, one at a
  time, never two runs against the REPL on 6666; `remote_error` means a
  golden YAML diff (`Tests/<name>.diff`). ML-only tests go through
  `theory_test(name, file)` in `IsaMini/AoA/test.py`, which runs a theory
  file through the REPL with no RPC.
- Never modify, regenerate or delete a golden YAML (`Tests/*.yml`)
  without the owner's explicit approval; new goldens are shown before
  trusted.
- Mutation checks act on the tests themselves: break each new check in
  memory (a pytest plugin or a monkeypatch) and watch its test fail.
- Shared working tree: no `git stash` / `checkout` / `reset --hard` /
  `clean`; commit only on the owner's word, on `main`, trailer
  `Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>`; stage only
  own paths; `ai-artifacts/review/` stays untracked; probes never committed.
- Design or plan documents: Edit tool only, never scripts.
- One term per concept; reuse over reinvention; elegance weighs as much as
  correctness; no flags, special cases or second mechanisms where one
  shape serves.
- Peers to notify, by their display names: the TAT session implementing
  the 17-step plan (`构建Isabelle代码生成Agent (3)`, the un-forked jobs
  session) and the TAT compile session (`构建Isabelle代码生成Agent (4)`),
  before Step 6 changes `hammer_or_AoA`'s record (TAT's `Theorem` drive
  path calls it). The owner: when Step 2 retires the proof-store plan's
  D31 note ("BinIO's instream cannot be fed from a string"), and for every
  text in §4.

## 3. Steps

Each step compiles and is testable on its own. Paths are under
`contrib/Isa-Mini/` unless noted.

The step texts are the original instructions of 2026-10-08. Where they
disagree with §3b, the spec or the code — names (`lookup_operation`,
`lookup_task`, `operations_of`, `activate_user_operations`,
`_is_sub_proof`, `check_class_registration`), the order of plugin
operations, file locations, field names — the spec and the code win, and
the ledger of §0 records the final state.

### Step 1 — Isabelle_RPC: `mk_callback` re-raises whatever escapes its read (spec §2)

File: `contrib/Isabelle_RPC/Tools/RPC.ML`, `mk_callback` (a separate
submodule: its own commit, bumped in the main repo later with the rest).

- Today: the outer `Exn.Exn` arm of the argument read answers
  `interrupted` and re-raises for an interrupt, and answers `failed exn`
  without re-raising otherwise; the dispatch loop then reads the stale
  `(cb_id, arg)` and the command dies of `protocol error`.
- Change: answer `interrupted` for an interrupt and `failed exn`
  otherwise, and re-raise in both cases (`(if Exn.is_interrupt exn then
  interrupted else failed exn, SOME exn)`); rename the flag `interrupt` to
  `reraise`; widen the comment from "an interrupt must re-raise" to
  "whatever escapes the read must re-raise".
- Test (RPC's own test theory or a probe under `ai-artifacts/probes/`): a
  callback whose `arg_schema` raises on a malformed argument ends the
  command with that error text, not `protocol error`; existing RPC tests
  still pass.
- Done when: loaded after a REPL restart, the test passes.

### Step 2 — one BinIO codec, in-memory streams (spec §2)

Files: `Agent/agent_packer.ML`, `Agent/agent_server.ML`,
`Test/Test_Agent_Packer_Recorded_Proof.thy`.

- `agent_packer.ML`: delete the functor `MiniLang_Agent_Pack`, the
  instances `ML_BinIO`/`ML_Bytes`, `xcmd_packer_bytes`,
  `xcmd_unpacker_bytes`, the commented-out serializer that used
  `ML_Bytes`, and the note "BinIO's instream cannot be fed from a string"
  (it is false: verified in Poly/ML 5.9.2 with `isabelle ML_process`).
  Write `packer`/`unpacker` once in `structure MiniLang_Agent` over
  `MessagePackBinIO` with `RPC_Term_Codec` instantiated on it.
- Export from `MINILANG_AGENT` two in-memory helpers:
  `instream_of_bytes : Word8Vector.vector -> BinIO.StreamIO.instream`
  (`BinIO.StreamIO.mkInstream (BinPrimIO.openVector v, Word8Vector.fromList [])`)
  and `bytes_of_output : (BinIO.StreamIO.outstream -> unit) -> Word8Vector.vector`
  (a `BinPrimIO.WR` whose `writeVec` appends slices to a ref, through
  `BinPrimIO.augmentWriter`, `BinIO.StreamIO.mkOutstream (wr, IO.BLOCK_BUF)`,
  the writes under `\<^try>… finally closeOut`, `Word8VectorSlice.concat
  (rev (!buf))`; so corrected by review round 1, F1). Names are the
  implementer's; keep them descriptive.
- `agent_server.ML`: the blob codec `encode_blob`/`decode_blob`, defined
  before `raw_AoA`, is the one place the blob layout lives (base64 of
  msgpack (split script, op stream)): `raw_AoA` encodes,
  `aoa_replay_method` decodes, and `Test_Agent_Packer_Recorded_Proof.thy`
  decodes with `decode_blob`.
- Test: an existing `aoa_replay "<b64>"` entry from a `.proof-store`
  decodes byte-identically (MessagePack bytes do not depend on the IO
  structure); the recorded-proof test theory passes.
- Tell the owner that the D31 note is retired.

### Step 3 — `agent_config.ML` and `agent_plugin.ML` (spec §1, §5.1)

Files: new `Agent/agent_config.ML`, new `Agent/agent_plugin.ML`,
`Agent/agent.ML`, `Agent/Minilang_AoA.thy`.

- `agent_config.ML`: `structure MiniLang_Agent_Config` with `budget`,
  `cfg`, `counters`, `datatype exec_mode = LIVE | REPLAY` and
  `type config = cfg * budget * counters * exec_mode`, moved verbatim from
  the top of `agent.ML` (both the signature copy and the structure copy).
  `MINILANG_AGENT` re-exports them as type abbreviations plus
  `datatype exec_mode = datatype MiniLang_Agent_Config.exec_mode`;
  `default_cfg` stays in `agent.ML`.
- `agent_plugin.ML`: `structure MiniLang_Agent_Plugin : MINILANG_AGENT_PLUGIN`
  exactly as spec §1 declares: `env`, `'a user_operation`, `registration =
  {operation : Universal.universal user_operation, python_packages}`,
  `task`, `user_operation_selection`, `register_user_operation` (a
  `Universal.tag ()` per registration; stored `unpack_arg` injects,
  `pack_arg` and `run` project), `register_task`, `lookup_operation`,
  `lookup_task`, `operations_of` (name order), `active_operations`
  (defaults ∪ includes − excludes; an unknown name raises an error naming
  it — text to propose). Two `Theory_Data` tables:
  `(serial * registration) Symtab.table` and the task table; insert with
  `Symtab.update_new`, merge with `Symtab.merge (eq_fst op =)`, and turn
  `Symtab.DUP name` into an error naming the operation or task (the
  importing theory then fails to load). `usual` and `learning` registered
  once via `Theory.setup` with `python_packages = []`.
- `Minilang_AoA.thy` load order: `helper.ML`, `agent_hint.ML`,
  `agent_config.ML`, `agent_plugin.ML`, `agent.ML`, `agent_packer.ML`,
  then as today.
- Tests (`theory_test`): `active_operations` with defaults, include,
  exclude, unknown name; duplicate registration of one name in two
  theories fails the importing theory; `lookup_task` of `usual` and
  `learning`.

### Step 4 — the `USER` command and `derived_subgoals_of` (spec §1, §2, §4.1)

Files: `Agent/agent.ML`, `library/proof.ML`.

- `agent.ML`, datatype `command`: add `| USER of string * Universal.universal`
  (same in `xcmd` and `icmd`). `check_command_i s (USER x) = USER x`.
- `interpret_i`'s `USER` branch, in this order: `lookup_operation` on the
  theory of `Minilang.context_of s` (NONE → `OPR_FAIL (INVALID_OPR, …)`,
  text to propose); `(s1, msgs) = Minilang.record_reporter (#run (#operation reg) config arg) s`;
  `derived = Minilang.derived_subgoals_of s s1 msgs`; if a schematic
  variable (term or type) occurs in two or more members of `derived`,
  raise `OPR_FAIL (PROOF_FAIL, <the approved refusal text>)`; else send to
  `Minilang.get_reporter ()` every message of `msgs` in order except the
  `Goals` ones, then one `Goals derived`; return `s1`.
- `read_method_text : Proof.context -> string -> Method.text` with
  `exec_split_script`'s parse as its body (`Parse.read_embedded ctxt
  (Thy_Header.get_keywords' ctxt) (Method.parser 0)` … `Method.check_text`);
  `exec_split_script` (agent_server.ML) and `try_cached_apply` (agent.ML)
  call it. Export from `MINILANG_AGENT`: `read_method_text`, `read_term`,
  `read_prop`, `check_authored_props`, `check_authored_terms`,
  `reject_undeclared_frees`.
- `proof.ML`, `derived_subgoals_of`: when the stack shrank return `[]`;
  when it grew (with or without an `ENDBLK` on top) return the first
  `Goals` message's goals, else the goals of the top `HHF` frame; when
  the depth is unchanged keep the current window. Delete the "Known
  boundaries" paragraph; the contract comment names the new caller (reads
  the real run, never preruns). Re-run the existing tests of the CaseSplit
  gate, the SplitConjs gate and the InferenceRule probe
  (`test_AoA.py -f` on their names).
- Tests of the branch itself come with the sample plugin (Step 9); a
  `theory_test` with a registration made inline in the test theory can
  cover the refusal and the one-`Goals` emission before Step 9.

### Step 5 — the codec's `USER` branch (spec §2)

File: `Agent/agent_packer.ML`.

- `packer` and `unpacker` take the theory (`theory -> xcmd packer`,
  `theory -> xcmd unpacker`); the three users pass it: `proof_opr`'s
  `arg_schema`, the blob assembly in `raw_AoA`, `aoa_replay_method`.
- `"USER"` branch of `unpacker`: read the name; `lookup_operation thy name`
  NONE → `error ("User operation \"" ^ name ^ "\": no imported theory registers it")`;
  else `(#unpack_arg (#operation reg)) handle Unpack => error ("User operation \"" ^ name ^ "\": its argument does not decode")`.
  Packer mirror: `packPair (packString, #pack_arg …) (name, arg)`.
- Tests (`theory_test`): round trip of an inline registration through the
  codec; a wrong payload gives the named error; an unknown name gives the
  named error.

### Step 6 — `agent_server.ML`: entry points, start of the call, messages, callers (spec §3, §5)

Files: `Agent/agent_server.ML`, `Agent/AoA_REPL/aoa_repl_app.ML`,
`Test/Test_Proof_Store_Hash_Hit.thy` (test 24),
`/home/qiyuan/Current/MLML/tasks/AoA-learning/learning.ML`,
`contrib/phi-system/Phi_Logic_Programming_Reasoner/library/reasoners.ML`
(separate submodule: own commit + bump). Notify the two TAT sessions first.

- Signatures (spec §5.1): `raw_AoA`, `run_AoA`, `hammer_or_AoA` gain
  `user_operations: MiniLang_Agent_Plugin.user_operation_selection`;
  `hammer_or_AoA` gains `task`; `task` is `MiniLang_Agent_Plugin.task`;
  delete `datatype task` and `pack_task`, send `(#name task, #payload task)`
  where `pack_task` was used. `method` and `hammer_or_aoa_method` pass
  `usual` and `[]`; `aoa_repl_app.ML` passes `usual` and `[]`;
  `learning.ML` passes `learning isar` and `[]`; `reasoners.ML` and test
  24 pass `usual` and `[]`.
- Start of the call in `raw_AoA` (spec §5.2), after the gate: the
  registrations from `active_operations` and `lookup_task` (NONE → error,
  text to propose); packages deduplicated; `Remote_Procedure_Calling.load`
  of them right after the existing `load ["IsaMini.AoA"]`; one local
  `current_config ()` built from the replay-mode ref, used by
  `proof_opr_callback`, `schematic_vars_of_derived_subgoals_callback` and
  `env`; `env = {state_of = Symtab.lookup o ! state, config = current_config}`;
  the registrations' `callbacks env` appended to `aoa_cmd`'s list after a
  name check against that list and `Remote_Procedure_Calling.get_global_callback`
  (error text to propose); the active names in name order added to the
  `IsaMini.AoA` argument beside the task.
- Messages (spec §3): `minilang_message_packer ctxt running_op` where
  `running_op : registration option`; inside, `pack_opt : message -> raw_packer option`
  with every built-in branch answering `SOME` (tags 0–20 as today), then
  `Internal e` → `Option.mapPartial (fn r => #pack_message (#operation r) e) running_op`
  packed as `(21, p)`; the function is `packList I o map_filter pack_opt`;
  the whitelist filter and the `BUG #adli` fallback go. `proof_opr`
  computes `running_op` (NONE unless the command is `USER`) with the same
  lookup `interpret_i` makes and hands it to the packer in `ret_schema`.
- Tests: the existing model tests (one with an `Induction` step) still
  pass — this proves no built-in message was lost; the Step 9 sample
  covers tag 21.

### Step 7 — Python model (spec §4, §5.2)

Files: `IsaMini/AoA/model.py`, `IsaMini/AoA/task.py`, a new module for
the base schema (name: implementer's, e.g. `edit_schema.py`), `test.py`.

- Base schema module: loads `tools/cc_edit.jsonc` once (`jsoncomment`);
  `model.py` and `mcp_http_server.py` import it; the decorators read its
  `$defs`.
- `UserNode` (mixin, listed before the base): `construct_schema`,
  `payload()`, `unpack_own_message(cls, value)` whose default raises
  `InternalError('User operation "<name>": its pack_message reported a message its node class does not decode.')`,
  `the_operation()` and `beginning_opr()` returning
  `Minilang_Operation("USER", (name, self.payload()))`,
  `can_operate_on_schematic_goal` calling the new module-level
  `_refuse_schematic_goal(state, op_name)` for a `SubgoalMaker` (built from
  `Branch`'s gate body, which `Branch` now calls too) and deferring to
  `super()` otherwise, `_execute_opr` override that after `super()` fails
  the step when the node is a `Leaf` and `dest.new_subgoals_count > 1`
  (raise `IsabelleError` with a text to propose), `_check_registration(name)`
  (the schema checks of spec §4.1). `Node._check_registration` no-op
  default.
- `@proof_operation`: before writing either registry, refuse a name held
  by a different `(module, qualname)`, an abstract class
  (`inspect.isabstract`), and a failing `_check_registration`.
  `TASK_REGISTRY` and `@aoa_task(name)` with the duplicate and
  abstractness checks; `task.py` registers `UsualTask` as `"usual"` and
  `LearningTask` as `"learning"`.
- `Runtime.operations: dict[str, OperationMeta]` and the forwarding
  property `Session.operations`; `Parse_Nodes` looks names up there and
  passes the table's names to `ArgumentError_UnknownProofOperation(arg, names)`.
- `unpack_message(data, user_cls)`: `Minilang_State.execute` computes
  `user_cls = the_session().operations[opr.arg[0]].cls if opr.command == "USER" else None`
  and passes it; the `(21, x)` arm returns `user_cls.unpack_own_message(x)`,
  or raises `InternalError` when `user_cls is None`.
- Approved cleanup: the four identical `_ending_opr_err_msgs` of
  `SplitConjs`, `InferenceRule`, `Branch`, `CaseSplit_Like` (each only
  raising `InternalError`) become one default on `SubgoalMaker`; the spec
  (§4.1) already describes the default and its example omits the hook.
- Tests (plain pytest, no REPL): decorator refusals (duplicate name,
  abstract class, each schema check); `Parse_Nodes` miss lists only the
  table's names; `unpack_message` bug guard.

### Step 8 — Python call start and schemas (spec §5.2, §5.3)

Files: `IsaMini/AoA/toplevel.py`, `mcp_http_server.py`,
`driver_openai_api.py`, `driver_gemini.py`, `driver_codex.py`, `test.py`.

- `toplevel.py`, `IsaMini_AoA`: unpack the active names and the task
  `(name, payload)` from the new argument fields; build the `Runtime`
  (operations table, task from `TASK_REGISTRY[name](payload)`) right after
  unpacking, before `_ensure_semantic_db`, `update_interpretations` and
  the driver split; refuse (spec §8) an active name with no class or a
  non-`UserNode` class, and a task name with no class; pass `runtime=` to
  the drivers and to `TestCase.run`, which `ModelTestCase` hands to
  `Session(runtime=...)`.
- `mcp_http_server.py`: `_tool_schemas_for(session)` builds the call's
  `edit` schema from the base plus `session.operations`' `construct_schema`s
  (`$defs/<name>`, `Operation.anyOf` appended in name order) and puts it in
  the `edit` entry it returns; `_TOOL_SCHEMAS["edit"]` keeps description
  and annotations only; delete `_cc_edit_schema_flat` and
  `_cc_edit_schema_codex`; keep `_assert_no_refs` as a function.
- `driver_openai_api.py`: `OpenAIBase._strict_schema` returns
  `_strictify_schema(_flatten_edit_schema(schema))` for `edit`;
  `DeepSeekProvider._strict_schema` returns
  `_flatten_edit_schema_deepseek(schema)`; delete
  `_cc_edit_schema_deepseek_cache` and `_deepseek_edit_schema`;
  `_flatten_edit_schema_deepseek` recognises a sub-proof field by the
  schema it refers to (`$ref` to `Proof` or `GivenLater`, an array of such,
  an object with such a required property), not by `_PROOF_KEYS`.
  `driver_gemini.py`'s `format_tools` uses `_flatten_edit_schema(info["schema"])`;
  `driver_codex.py`'s `transform_tool_schema` uses
  `_merge_edit_operations_schema(_flatten_edit_schema(schema))`.
- Tests: a `Session` over a `Runtime` whose operations include `Apply`:
  `_tool_schemas_for(session)["edit"]["schema"]` has the `Apply` branch,
  all four derived forms have it and pass `_assert_no_refs`; the DeepSeek
  form of the base schema is byte-identical to today's output (capture it
  before the change).

### Step 9 — the sample plugin and the spec's §9 tests

Files: the plugin theory `IsaMini/AoA/Tests/Sample_Plugin.thy` (importing
`Minilang_AoA.Minilang_AoA`), the package `IsaMini/AoA/Tests/sample_plugin/`
(a package of the test tree), fixtures under `IsaMini/AoA/Tests/`, `test.py`;
the theory tests under `IsaMini/AoA/Tests/` as well.

- Registrations: `Apply` (`default = true`, one message of its own, a
  `SubgoalMaker` with `unpack_own_message`); the `StdBlock` sample whose
  `run` is `MiniLang_Agent.interpret config (HAVE …)`; a `Leaf` sample
  whose `run` leaves two subgoals and forwards no `Goals`; a `SubgoalMaker`
  sample composing `CONSIDER`; a `StdBlock` sample whose sub-proof field
  is named `proof`, parsed by the base (schema test only, in pytest; so
  corrected by review round 1, Q4).
- Tests, each a `@model_test` with its own `.thy` fixture unless noted:
  `Apply` fill and render (golden YAML, owner approval), the message
  reaching `unpack_own_message`, an `Induction` step in the same call; the
  replay test (the blob `encode_blob` builds, replayed by `aoa_replay`);
  the `StdBlock` sample opened by the operation and closed by `END`, also
  on a goal with schematic variables, and its stored proof replayed
  through `aoa_replay` (the replay theory test's block case; SP-3); the
  `Apply` test `(rule trans[of a b c])` then
  `(rule trans)` into the same destination name (refused naming `?s`, the
  name still holds the first result); the `CONSIDER` sample refused by
  `_gate_rejection`; the `Leaf` sample failing with the one-subgoal error;
  a plugin whose `payload()` mismatches `unpack_arg` (the call ends with the
  named error); a plugin whose `pack_message` answers `SOME` but whose
  class has no decoder; `active_operations` and the §8 refusals one each.
- Mutation checks on every new check.

### Step 10 — documents and notices

- `IsaMini/AoA/docs/DEVELOP.md` and `AGENTS.md`/`CLAUDE.md` (both copies):
  file-map rows for `agent_config.ML`, `agent_plugin.ML`, the base schema
  module, the sample plugin; one paragraph pointing at the spec.
- Propose to the owner the texts of §4 below; notify the owner about D31
  (Step 2) and the TAT sessions about the signatures (Step 6) if not done.

## 3b. Code review round 1 (2026-10-08) — the fixes, and where they stand

The judge's ruling is in `<scratchpad>/code_review.json` (findings, defenses,
judgement). The owner decided: Q1 (b) `USER` keeps the name, `the_operation`/
`the_task` hold the text; Q2 no guard (a plugin's duty, §7); Q3 keep the
mixin; Q4 sub-proof fields are named `proof`/`proofs` by convention, DeepSeek
removes by name again; Q5 the four tactic texts (`Outer syntax error: <text
marked>`, `Unexpected text after the tactic: <marked>`, `The tactic text is
empty.`, `Undefined tactic: "x"`), marked with `Inner_Syntax_Error`'s marker;
Q6 bound the sample's Apply; Q7/Q8 tests are the implementer's; Q9 plugin
operations in REGISTRATION order (the serial), Python keeps the order received,
ML sorts nowhere else; Q10 the pretty.ML comment goes.

Done (uncommitted): all ML fixes (`agent_plugin.ML` the_*/serial order/`selected`,
`agent.ML` the reader with markers, `agent_packer.ML` closeOut + BLOCK_BUF, dead
line, `agent_server.ML` encode_blob/decode_blob before raw_AoA, `packPair (_, I)`,
comments, `the_task`), Isabelle_RPC (`inner_syntax_error.ML` exports `marker`,
`mark_window`, `last_offset`, `clean_prose`; `pretty.ML` comment; `RPC.ML`
arg_schema comment; the RPC test matches `ERROR`), the sample plugin (named
cases, time bound, TwoGoals forwards no Goals, `_initial_goal_index = 0`),
`Tests/User_Operation_Test_Base.thy` and the five test theories rewritten
(registry/interpret/codec pass under the ML_process probe; replay and call
need the REPL), Python (helper `check_class_registration`, `BUILTIN_OPERATIONS`,
`Runtime(user_operations)`, Leaf assert, key-name sub-proof rule, docstrings,
`task_name`, packaging), `test_user_operations.py` 29 green + 6 new mutants
killed, `test.py` Consider rewritten (sibling schematic) + `UserOp_ConsiderCases`
new, fixtures written. `UserOp_Consider.yml` was deleted for regeneration (the
review ruled it; to be shown to the owner).

Verified after the fixes (REPL on 6666, now stopped): the nine `UserOp*`
model tests, Branch1, Induction_NoSimp, InferenceRuleSolvesGoal, GateSchematic,
the store and recorded-proof theories, the RPC callback test, and — after
the replay goal became the opaque `PP` and `message_of` was added to the test
base — `UserOperationReplay_Minilang` and `UserOperationCall_Minilang`;
`UserOp_TwoGoals.yml` byte-identical. pytest 29 green, 6 new mutants killed.

Documents brought to the final state: the spec (§1 signature block and the
order sentence, the reader sentence, §2 `the_operation`, §4.1 the naming
convention, §5.2 steps 1 and 4, §5.3 order / fork / each flattening's own
`_assert_no_refs` / the two flattenings' sub-proof rules, §7 two bullets, §8
the four tactic texts and the `Runtime` label, §9 locations, `proof`, the
ApplyShared order, the codec substitution), DEVELOP.md (the sample as the
template), ledger rows 1/2/3/6/9.

Code review round 2 (2026-10-09; 7 reviewers, 66 findings, one fresh
defender each, one judge; the record is `<scratchpad>/code_review_round2.json`).
The judge accepted 36 items (A1–A36), rejected 16, asked three questions; the
owner answered OQ1 (a) reuse `Outer syntax error: <marked>` for a text that
does not tokenize, (b) reuse `Undefined tactic` for an inaccessible name
(the implementer's reading of "赞同 (a)", flagged); OQ2 "随便" (no change);
OQ3 the skill-file update last, after the owner's own review; and OQ4, the
implementer's question whether the order between plugin theories that do not
import each other should be deterministic: NAME order, replacing Q9.

Done: all 36 items, as the ledger rows record (A1 the reader; A2/A5/A6/A14/
A15/A29/A34 the theory tests; A3 exact-match reader cases; A4 the mutation
ledger; A7/A10/A11/A18/A23/A27/A35/A36 the spec; A8/A9/A12/A13/A16/A17/A31/A32
Python; A19 this plan; A20/A21/A22 agent_server.ML; A24 DEVELOP.md; A25/A26
Inner_Syntax_Error; A28 the registry helpers; A30/A33 comments). Verified
(fresh REPL on the final sources, then stopped): the 5 theory tests and the 8
`UserOp_*` model tests (13/13), `Test_Callback_Argument`,
`Test_Agent_Packer_Recorded_Proof`, `Test_Proof_Store_Hash_Hit`, Branch1,
Induction_NoSimp, InferenceRuleSolvesGoal, GateSchematic; pytest 32. Mutation
checks, each mutant applied to the sources, the REPL restarted, the targeted
test run, the sources restored and compared byte-for-byte: 20 ML or
theory-side mutants in 7 batches (the targets of one batch in different test
theories), all killed by exactly their target; 4 Python mutants in memory,
one per process, all killed. The tool: `<scratchpad>/mutate.py` and
`mutant_batch.sh`.

OQ3 closed 2026-10-09: the owner's rule is that nothing new goes into a
skill file (existing concepts may be changed or removed). The isabelle-rpc
skill's `Inner_Syntax_Error` entry lists eight exports, all still present
with their types, and describes a mechanism this change kept, so nothing
in it became wrong; the four newly public names (`last_offset`, new; `marker`,
`mark_window`, `clean_prose`, exported now) and the old omission of
`positioned_id` stay out of it. The skill file is untouched.

Code review round 3 (2026-10-09; 4 reviewers on the round-2 code changes only,
20 findings, one fresh defender each, one judge; the record is
`<scratchpad>/code_review_round3.json`). The judge accepted 16 items (5 minor,
11 nit), rejected 4, asked nothing of the owner, and no agent-visible text
changed. The owner had authorised the commit once the round passed. Done:
- R1-1 `Inner_Syntax_Error.decode`: a message that is not well-formed YXML
  (one quoting chr 5 / chr 6 of the failed text) decodes to its plain text, so
  locating a failure never raises; the reader then answers the unmarked text;
  R1-3 `clean_prose` is no longer exported (nothing outside the module used
  it); R1-2 the reader's two failure functions became one `located` plus
  `fail prefix`, the probe through `Exn.result` (interrupts pass);
- R2-1 toplevel.py's comment says name order; R2-2 the registry test
  compares the approved texts exactly; R2-4 one phrase for the order the
  classes were registered in;
- R3-1 `_strictify_schema` walks a `properties` map as field names, so a
  plugin field named `properties` keeps its schema and both forms stay valid
  (pinned with jsonschema's check_schema); R3-3 a test of the `simplify`
  hint; R3-4 the built-ins check is `_check_builtins_advertised`, tested;
  R3-5 "field" throughout the DeepSeek derivation;
- R4-1 the Interpret test's long cases compared exactly and two true
  mid-text cases (both ellipses; the syntax-error path and the leftover
  path), the windows computed by mark_window's rule by hand and confirmed
  in the run; R4-2 the `(aut)` comment; R4-4 one `argument` helper in the
  test base; R4-5 the two test.py comments; R4-6 `Exn.result` in
  `failure_of` and `refused`; R4-7 the vacuous "the block is open" line gone.
Verified on a fresh REPL: the 5 theory tests and 8 model tests (13/13),
then after the mutant below the RPC test, both Test/ theories, 13/13 again
and the four regression model tests (recorded in the paragraph that
follows); pytest 34. Mutants, all killed: Python (in memory, one per
process) the properties map walked as a schema node again, the simplify
hint deleted, the built-ins check inverted, its two lists swapped; ML (REPL
restart, sources restored byte-for-byte) the decode guard removed, which let
yxml.ML's Fail escape exactly as the finding traced.

Committed 2026-10-09 (authorised by the owner for after round 3): Isa-Mini
62f6b89 (own paths plus the TAT session's two riding changes), Isabelle_RPC
6d09e25, phi-system 23a18343 (`reasoners.ML` only), the main repo d91a7de2
(`learning.ML` and the three submodule pointers). Not staged, not mine:
`PlainAgent/`, `IsaMini/AoA/docs/TACTIC_DESIGN.md`, the
`Performant_Isabelle_ML` pointer; the `Query*`/`SemanticKNN_*`
`.actual.yml`/`.diff` files under `Tests/` are the environmental golden
diffs of the earlier regression run, left for the owner.

Follow-up (2026-10-09, the two items TAT's review passed on, both taken on
the implementer's recommendation and the owner's go-ahead): `method_error`
in `agent_server.ML`, the one rendering of what an agent run raises (a
give-up under its banner, the engine's Internal_Failure by its message,
anything else re-raised), exported for TAT's construct to call in place of
its copy, used by the `aoa` and `hammer_or_aoa` methods; the signature
comment of `replay_record` in `proof_store_AoA.ML` says what the function
does and no longer names its caller.

## 4. Texts

Approved (verbatim in the spec):
- codec errors: `User operation "Aply": no imported theory registers it`;
  `User operation "Apply": its argument does not decode` (§2);
- the shared-schematic refusal (§4.1): `Apply left the schematic variable
  ?y in more than one of the subgoals it produced. A schematic variable may
  be left in at most one subgoal, so this step is rejected.` (plural: `the
  schematic variables ?x, ?y`);
- `unpack_own_message` default: `User operation "Apply": its pack_message
  reported a message its node class does not decode.` (§4.1).

Approved by the owner on 2026-10-08, after implementation, and now quoted
verbatim in the spec's §8 (the list below is what was proposed):
- `interpret_i`'s `INVALID_OPR` text for an unregistered name reached at
  execution (store replay path) — the §2 text reused;
- `active_operations`' unknown-name error (the §2 text reused);
  `lookup_task`'s NONE error;
- the callback-name clash error (against `aoa_cmd`'s list and the global
  callbacks);
- the `Leaf` one-subgoal error (`UserNode._execute_opr`);
- the decorator refusals (duplicate name, abstract class, each schema
  check); the start-of-call refusals in `toplevel.py` (no class under an
  active name, class not a `UserNode`, no task class);
- the `Symtab.DUP` errors at registration and merge.

Note (review round 2, A19): the first bullet's premise was wrong — no
`INVALID_OPR` text exists on the store replay path; since Q1 (b) the text
for an unregistered name, wherever it is reached, is the ERROR
`the_operation` raises, and `lookup_task` is `the_task`, which raises
likewise. The list stays as the record of what was proposed.

The seven goldens `Tests/UserOp_*.yml` were approved the same day; the
regenerated `UserOp_Consider.yml` and the new `UserOp_ConsiderCases.yml`
on 2026-10-09. Round 2 added no agent-visible text: the owner chose, for
the two failures of method text the four texts did not cover, to reuse
`Outer syntax error: <marked>` for a text that does not tokenize (OQ1 (a))
and `Undefined tactic: "Thy.foo"` for an inaccessible name (OQ1 (b), the
implementer's assumption, flagged); the sample plugin's agent-visible
wording stays (OQ2, "随便", the implementer chose no change).
