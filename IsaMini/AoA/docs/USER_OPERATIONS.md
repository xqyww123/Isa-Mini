# User-defined proof operations and tasks

Status: implemented. The design was settled 2026-10-06 and revised after two
design reviews, the last on 2026-10-07; the implementation passed three
adversarial code reviews, 2026-10-08 to 2026-10-09 (the record:
`ai-artifacts/USER_OPERATIONS_IMPLEMENTATION_PLAN.md`).

> References use stable symbol names, never line numbers — line numbers drift.
> Grep for the symbol.

A **plugin** adds proof operations, tasks, or both to AoA without editing
AoA. It has two halves: an Isabelle theory (the ML half), which registers
what the plugin provides and names the Python package that is its other
half, and that Python package (the Python half), which defines the agent's
view of each operation — its JSON schema, its node class, its rendering —
and the encoding the two halves talk in. A `by aoa` sees exactly the
plugins whose theories it imports.

A **user operation** is a proof operation like `Have` or `Witness`, defined
by a plugin: a name, a transition function on Minilang's proof state (ML),
and a node class with a schema (Python). A **user task** is a task like
`learning`, defined by a plugin: a name and a `Task` subclass (Python); its
payload is built by whoever calls AoA (ML). Which user operations one AoA
call activates is a parameter of that call (§5).

**What AoA trusts.** A plugin is trusted code: its ML runs with the
framework's authority, and AoA does not defend itself against it. What is
checked at import, at registration and at the start of a call (§8) turns a
mistake into an early refusal that names it; a mistake nothing checks for
surfaces where it happens, as the plugin's bug. The agent is not trusted:
its every input is checked as before.

Running example throughout: a plugin `Apply` whose one operation applies an
Isabelle proof method, given as text, to the current goal.

---

## 1. The ML half

A plugin theory imports `Minilang_AoA.Minilang_AoA` and registers through
`MiniLang_Agent_Plugin` (`Agent/agent_plugin.ML`). The load order of
`Minilang_AoA.thy` is `helper.ML`, `agent_hint.ML`, `agent_config.ML`,
`agent_plugin.ML`, `agent.ML`, `agent_packer.ML`, then the rest as today:
the registry loads before the interpreter that consults it, as `Agent_Hint`
does. `agent_config.ML` holds `MiniLang_Agent_Config` — `budget`, `cfg`,
`counters`, `exec_mode` and `config`, moved there from `agent.ML` verbatim;
`MINILANG_AGENT` re-exports them as type abbreviations and
`datatype exec_mode = datatype MiniLang_Agent_Config.exec_mode`, so every
existing `MiniLang_Agent.config`, `LIVE` and `REPLAY` keeps working.

```sml
signature MINILANG_AGENT_PLUGIN = sig
  type state_id = string
  type env = {
    state_of : state_id -> Minilang.state option,  (* raw_AoA's state table, by name *)
    config   : unit -> MiniLang_Agent_Config.config } (* the config of the moment it is read *)

  (* what a plugin writes, at its own argument type *)
  type 'a user_operation = {
    name         : string,                                  (* the agent-facing operation name *)
    default      : bool,                                    (* active in every call unless excluded (§5) *)
    unpack_arg   : 'a MessagePackBinIO.Unpack.unpacker,
    pack_arg     : 'a MessagePackBinIO.Pack.packer,
    run          : MiniLang_Agent_Config.config -> 'a -> Minilang.operation,
    pack_message : exn -> MessagePackBinIO.Pack.raw_packer option,
    callbacks    : env -> Remote_Procedure_Calling.callback' list }

  (* what the registry holds: the plugin's record over Universal.universal, and its packages *)
  type registration = {
    operation       : Universal.universal user_operation,
    python_packages : string list }

  type task = {name : string, payload : MessagePackBinIO.Pack.raw_packer}
  type user_operation_selection = (string * bool) list     (* (name, include?) *)

  val register_user_operation :
        {python_packages : string list} -> 'a user_operation -> theory -> theory
  val register_task :
        {python_packages : string list} -> {name : string} -> theory -> theory

  (* what the framework reads; a name no imported theory registers is an error *)
  val the_operation     : theory -> string -> registration
  val the_task          : theory -> string -> {python_packages : string list}
  val active_operations : theory -> user_operation_selection -> registration list  (* name order *)
end
```

**The registries.** Two `Theory_Data` tables, one for operations and one
for tasks, each a `Symtab` keyed by name whose entries carry a serial.
`register_user_operation` and `register_task` insert with
`Symtab.update_new`; merging is `Symtab.merge (eq_fst op =)`; in both, a
`DUP` becomes an error naming the operation or task, so a theory importing
two plugins that share a name fails to load. A registration reached through
two import paths counts once, and re-evaluating a registering theory
registers once. `the_operation` and `the_task` are `Symtab.lookup` raising
`User operation "X": no imported theory registers it` (`User task "X": …`)
on a miss, defined everywhere replay runs, so every text that names a
registration's absence is written once. Where an order is visible —
`active_operations`, the `anyOf` of the assembled schema, the names sent to
Python — it is name order: `active_operations` sorts the names with
`string_ord` (not the table's own `fast_string_ord`, which compares lengths
first), nothing else in the ML sorts, and Python keeps the order it
receives. The serial an entry carries serves the merge alone, never the
order: the order in which plugin theories that do not import each other
run their registrations is the scheduler's, so an order read from the
serials would differ between builds.

**The argument type.** `register_user_operation` hides the plugin's `'a`
with a `Universal.tag ()` of its own, as `Thread_Data.var` does: the stored
`unpack_arg` injects what the plugin's unpacker reads, and the stored
`pack_arg` and `run` project it back before calling the plugin's functions.
One registration's tag is the only one ever applied to that registration's
values, so a projection cannot fail. A plugin writes its three argument
functions at its own type and sees, for the argument, neither
`Universal.universal` nor a wrapping exception; a mismatch between
`unpack_arg`, `pack_arg` and `run` is a type error. Its messages are its
own exceptions (§3).

**`run`.** `Minilang.operation` is `Minilang.state -> Minilang.state`
(`library/proof.ML`). `run` receives the config built for its own
execution, whose `exec_mode` says whether this is a live run or a replay,
as `HAMMER` reads it.

Text the agent wrote reaches Isabelle only through `MiniLang_Agent`'s
readers, which carry positions, reject undeclared free variables and apply
the theory's `Agent_Hint` entries; `Minilang`'s functions are the layer
below those checks. A user operation therefore either composes a built-in
command, `MiniLang_Agent.interpret config (HAVE …)`, or reads with
`read_term`, `read_prop` or `read_method_text` and checks with
`reject_undeclared_frees`, `check_authored_terms` and `check_authored_props`
— all exported from `MINILANG_AGENT`; `read_method_text` is the one reader
of method text, which `exec_split_script` and `try_cached_apply` call too:
it reads the plain text, as before, and only on a failure reads the same
text again positioned, a probe whose value is never used, to mark the
failing spot with the marker `read_term`'s failures use; every failure
comes back as one of the four texts of §8, never as a text of Isabelle's,
the undefined-name text built from the name the agent wrote. Terms inside method text are
read only when the method runs, so an operation that applies method text
is outside `Agent_Hint`'s reach. A `run` that executes text the agent wrote
bounds it in time, as the sample passes `mini_single_cmd_timeout` (§7).

When `run` composes several `Minilang` steps, it runs them with their
reports captured, through `Minilang.record_reporter`, as
`schematic_vars_of_derived_subgoals_callback` does; a single tactic step may
instead go through `Minilang.raw_apply_state` with a report of the author's
own, as `resolve_intro_state` does. `run` then forwards through
`Minilang.get_reporter ()` the captured messages its result needs,
`New_Items` and `Newly_Fixed` included. A `Goals` that `run` forwards is
read only to find the cases of a block it opens (§7). `interpret_i`'s
`USER` branch records around `run` too and forwards what `run` reported,
its `Goals` messages replaced by one `Goals` of the derived subgoals (§2);
the outer recording sees only what `run` chose to forward.

The running example:

```sml
val _ = Theory.setup (MiniLang_Agent_Plugin.register_user_operation
  {python_packages = ["isamini_plugin_apply"]}
  {name = "Apply", default = true,
   unpack_arg = MessagePackBinIO.Unpack.unpackString,
   pack_arg = MessagePackBinIO.Pack.packString,
   run = fn _ => fn text => fn s =>
     let val ctxt = Minilang.context_of s
         val bound = Time.fromMilliseconds (Config.get ctxt Minilang.mini_single_cmd_timeout)
      in Minilang.APPLY'' (SOME bound) [] (MiniLang_Agent.read_method_text ctxt text) s end,
   pack_message = K NONE,
   callbacks = K []})
```

Errors: `run` raises `Minilang.OPR_FAIL` with the kind that fits —
`TERMLANG` for a term or method the agent wrote that does not parse,
`PROOF_FAIL` when the step does not go through — or plain `ERROR`;
`proof_opr`'s existing mapping turns either into the failure of that step,
the text the agent sees.

---

## 2. The wire, the store and replay

`MiniLang_Agent.command` gains one constructor, the same in `xcmd` and
`icmd`:

```sml
| USER of string (*name*) * Universal.universal (*argument*)
```

**One codec.** The `xcmd` packer and unpacker (`agent_packer.ML`) are
written once, over `MessagePackBinIO`, and take the theory: the `"USER"`
branch reads the name, looks the operation up, and reads the argument with
that registration's `unpack_arg`, in place; the packer writes it with
`pack_arg`. The branch fails in two ways, each an `error` that names the
operation: for a name no registration carries, `the_operation` raises
`User operation "Aply": no imported theory registers it`, where the
existing `"Unknown operation"` arm raises for a built-in; and the branch
itself catches `Unpack` from `unpack_arg`, because `read_argument`'s own
handler would turn a bare `Unpack` into a text that names nothing —
`User operation "Apply": its argument does not decode`. Since there is one
codec, this covers `IsaMini.proof_opr`, the prerun callback, the store and
replay. The same codec serves the live wire, the store and replay. For the
store and replay the streams are in memory: an instream from
`BinIO.StreamIO.mkInstream (BinPrimIO.openVector v, …)`, an outstream over
a `BinPrimIO.WR` whose `writeVec` appends to a buffer, as `RPC.ML` and
Isabelle's `socket_io.ML` build streams from primitive readers and writers.
The functor `MiniLang_Agent_Pack`, `ML_Bytes`, `xcmd_packer_bytes` and
`xcmd_unpacker_bytes` go; `raw_AoA`'s blob assembly, `aoa_replay_method`
and `Test/Test_Agent_Packer_Recorded_Proof.thy` use the in-memory streams.
MessagePack bytes do not depend on which IO structure wrote them, so every
existing `aoa_replay "<b64>"` entry decodes as before. The note in
`agent_packer.ML` that BinIO's instream cannot be fed from a string is
false and goes with the functor.

- **Python → ML.** The Python half sends `("USER", (name, value))` through
  `IsaMini.proof_opr` as every operation is sent (`Minilang_State.execute`).
- **A read that fails.** The two errors above are raised inside the
  callback's argument read, before any operation runs.
  `Remote_Procedure_Calling.mk_callback` answers every exception that
  escapes its read region — an interrupt as `interrupted`, anything else
  as `failed exn` — and then re-raises it. Today it re-raises an interrupt
  alone: another read failure is answered but the dispatch goes on with
  the stream out of step, so the call dies of `protocol error`. With the
  rule widened the call ends with the error the `USER` branch raises. This
  is a change to `Isabelle_RPC/Tools/RPC.ML`; every existing callback's
  reads already end the call, and afterwards do so with their real error.
- **`check_command_i`** passes `USER` through. **`interpret_i`**'s `USER`
  branch looks the name up in the theory of `Minilang.context_of s` and
  runs `#run (#operation reg) config arg` under `Minilang.record_reporter`.
  It applies `Minilang.derived_subgoals_of s s1 msgs` (§4.1) and raises
  `OPR_FAIL (PROOF_FAIL, msg)` when a schematic variable occurs in two or
  more of the derived subgoals; otherwise it forwards `msgs`, in order,
  with every `Goals` removed, then exactly one `Goals` of those derived
  subgoals — the emit at the boundary the agent sees, as `AUTO_INTRO`'s is
  — to `Minilang.get_reporter ()`, and returns `s1`.
- **The proof store.** The assembled proof is the `xcmd` list, packed by
  the codec above; `pack_arg` and `unpack_arg` must round-trip, which the
  replay test checks (§9).
- **Replay.** `aoa_replay_method` decodes the blob in the context of the
  `by aoa` being replayed and runs `interpret` as today, so a stored proof
  replays only where the plugin theory is still imported. Elsewhere the
  entry is stale, as is any entry that no longer decodes: its replay fails
  and `run_AoA` falls through to `raw_AoA`; under an interactive frontend,
  or with `AOA_ALLOW_NONINTERACTIVE=yes`, `by aoa` proves afresh, and with
  the gate closed the batch build fails with the gate's error. The plugin
  owns the compatibility of its argument's encoding: `unpack_arg` keeps
  reading every layout an earlier release wrote, through `||` alternatives,
  as `unpack_extended_fact` does (§7).

---

## 3. Messages from ML to Python

An operation reports to Python by sending `Minilang.message` values through
`Minilang.get_reporter ()` while it runs; `proof_opr` collects them and
returns them with the new goal, and `Minilang_State.execute` decodes them
with `unpack_message` into the state's `messages`. The goal count, newly
fixed variables and new facts are the built-in messages `Goals`,
`Newly_Fixed` and `New_Items`, which a user operation sends as the built-in
operations do; for a `USER` step Python receives exactly one `Goals`, the
one the `USER` branch sends (§2).

A plugin's own message is its own exception sent as `Minilang.Internal e`,
exactly as `DEFINE_RESULT` and `COMPUTE_RESULT` are. The packer is one
partial function, `pack_opt : Minilang.message -> raw_packer option`, local
to `minilang_message_packer` and closing over the running operation as
today's `pack` closes over `ctxt`: each built-in branch answers `SOME` with
its tag — these branches replace both today's whitelist filter and the
`BUG #adli` fallback — and `minilang_message_packer` is
`packList I o map_filter pack_opt`. For an `Internal e` no built-in branch
claims, `pack_opt` asks the `pack_message` of the operation that is
running: `proof_opr` interprets exactly one command, so it looks the
running `USER` operation up — the lookup `interpret_i` makes — and hands it
to `minilang_message_packer`, which writes the answer as `(21, p)`. `NONE`
drops the message, as `IH_MAP` and `REPLACE_CMD` are dropped today. A
`pack_message` is asked only about messages reported while its own
operation runs; a `run` that calls another plugin's helper claims that
helper's exceptions in its own `pack_message`. On the Python side
`Minilang_State.execute`, the one caller of `unpack_message`, looks the
running operation's class up once — `session.operations[opr.arg[0]].cls`
when `opr.command == "USER"`, else `None` — and passes it to
`unpack_message(msg, user_cls)` as a required parameter; the `(21, x)` arm
answers `user_cls.unpack_own_message(x)` (§4.1), and raises an
`InternalError` when `user_cls` is `None`, a bug guard like the `case _`
arm.

---

## 4. The Python half

The package is importable in the Python environment AoA runs in. Importing
it registers its classes, as importing `IsaMini.AoA` registers the built-in
ones; the process-wide registries are `OPERATION_REGISTRY` (`model.py`)
and, new, `TASK_REGISTRY` (`task.py`, beside the `Task` classes).
`tools/cc_edit.jsonc` is loaded by `edit_schema.py`, which both `model.py`
and `mcp_http_server.py` import, so the decorators can read its `$defs`.

### 4.1 A user operation's node class

A node class of a plugin derives from the mixin `UserNode`, listed first,
and from one of `Leaf`, `SubgoalMaker`, `StdBlock` — the same choice the
built-in classes make — and is registered with the existing
`@proof_operation(name, ToolArg)`. `name` must equal the ML registration's
`name`. The class implements what any node class does — the constructor
its base's `gen_single` calls: `__init__(config, arg)` for a `Leaf`, whose
body calls `super().__init__(config, thought)`, and for a `SubgoalMaker`,
whose body calls `super().__init__(config, thought, [])`;
`__init__(config, arg, parsed_proof)` for a `StdBlock` that is not a
`SubgoalMaker`, `parsed_proof` the parsed `proof` field, stored in
`self._proof` as `Have` does (`UserNode` attaches it at the first refresh,
in its `_refresh_the_beginning_opr`, as each built-in block attaches its
own), while per-subgoal proofs on a `SubgoalMaker` are parsed by the
class's own `gen_single`, as `InferenceRule` and `Branch` do; `quickview_title`;
`print` for a `Leaf` or `_print_header` for the block bases; and the block
bases' error-text hooks `_beginning_opr_err_msgs` and
`_child_refresh_failure_err_msgs`, plus `_ending_opr_err_msgs` for a
`StdBlock` that is not a `SubgoalMaker` (a `SubgoalMaker` has no ending
operation, and supplies the default, which raises an `InternalError`) —
and what `UserNode` adds:

| member | what it is |
| --- | --- |
| `construct_schema: dict` | this operation's `$defs` entry of the `edit` schema (§5.3): `properties.operation` a `const` of the name, `thought`, the fields, `description`, `additionalProperties: false`; a sub-proof field is named `proof` (one sub-proof) or `proofs` (a list of them), and no other field, at any depth, is named so: `_flatten_edit_schema_deepseek` drops fields by these names (§5.3) |
| `payload(self) -> Any` | the Python value sent as the argument; Isabelle text in it already through `ascii_of_unicode`, as the `Minilang_Operation` factories do |
| `unpack_own_message(cls, value) -> Message` | decodes a tag-21 message of this operation (§3); `UserNode`'s default raises an `InternalError` naming the operation — `User operation "Apply": its pack_message reported a message its node class does not decode.` |

`UserNode` supplies `the_operation()` (for a `Leaf`) and `beginning_opr()`
(for the two block bases), both returning
`Minilang_Operation("USER", (name, self.payload()))`, and
`can_operate_on_schematic_goal`, which gates a `SubgoalMaker` (below).

**At decoration.** `@proof_operation` checks before it writes either
registry, and raises on a violation, which fails the import:

- the name is not held by a different class — two classes are the same
  when `(cls.__module__, cls.__qualname__)` is equal, so a re-import after
  a failed import registers again — built-in names included;
- `inspect.isabstract(cls)` is false: a `UserNode` listed after its base,
  or a forgotten hook of the base, would otherwise raise `TypeError` in
  the middle of a run;
- `cls._check_registration(name)` passes — `Node` supplies a no-op default;
  `UserNode`'s checks `construct_schema` against the JSON meta-schema,
  requires `additionalProperties: false` and `operation` a `const` equal to
  the name, requires every `$ref` to resolve into the base `$defs` and none
  to name `Operation` directly (a sub-proof field refers to `Proof` or
  `GivenLater`), and refuses a name that is a key of the base `$defs`.

The running example:

```python
class Apply_ToolArg(TypedDict):
    thought: NotRequired[str]
    method: str

@proof_operation("Apply", Apply_ToolArg)
class Apply(UserNode, SubgoalMaker):     # a method leaves N subgoals, each a child GoalNode
    construct_schema = {
        "type": "object", "additionalProperties": False,
        "description": "apply an Isabelle proof method to the current goal",
        "properties": {
            "operation": {"const": "Apply", "type": "string"},
            "thought": {"$ref": "#/$defs/Thought"},
            "method": {"type": "string", "description": "Isabelle method text, e.g. `(simp add: foo)`"}},
        "required": ["operation", "thought", "method"]}
    def __init__(self, config, arg):
        super().__init__(config, arg.get("thought", ""), [])   # StdBlock's third argument: the child nodes
        self.method = arg["method"]
    def payload(self):
        return ascii_of_unicode(self.method)
    def quickview_title(self):
        return f"Apply {self.method}"
    def _print_header(self, indent, file, ...):
        ...                                   # `operation: Apply`, `method: …`
    def _beginning_opr_err_msgs(self, err):   # as InferenceRule frames them
        ...
    def _child_refresh_failure_err_msgs(self, child):
        ...
```

Children are numbered by `SubgoalMaker` itself (`_new_goal_node`), as
`InferenceRule`'s are; `Apply` has no `proofs` field, so its children
start empty.

**The derived subgoals of a user operation.** A `SubgoalMaker` plugin
class opens, when its result has two or more derived subgoals, one child
`GoalNode` per subgoal, as `InferenceRule` does; with one subgoal or none
the result stays on the operation's own line (`_should_open_proof_block`).
The children are proved independently.
The built-in subgoal makers keep one invariant for their derived subgoals —
no schematic variable shared by two or more of them, since a sibling would
otherwise commit the choice for another — by probing and instantiating
before the operation commits (`_POST_INST_COMMANDS`,
`Interaction_InstantiatePostSchematics`; `SplitConjs` and `Branch` keep it
only by refusing at input). A `USER` command carries no instantiation
rounds, so the framework checks and does not repair, and
`_POST_INST_COMMANDS` stays keyed on built-in command names, which a `USER`
command never enters. The check sits in `interpret_i`'s `USER` branch (§2),
on the real before-state, the real after-state and the operation's own
messages, through `Minilang.derived_subgoals_of`: when the operation kept
the stack depth, the goals that replaced goal 1 of the frame; when it
opened a block, the first `Goals` message's goals — every case of a block
included — or, for a block opened without one as `HAVE` opens it, the new
block's goals; when it closed a frame, none. A schematic variable occurring
in two or more of them fails the step with `OPR_FAIL (PROOF_FAIL, msg)`.
Because it raises inside `interpret`, a refused step leaves `proof_opr`'s
state table as it was, as every step that fails inside ML does; the check runs wherever
a `USER` command runs, `aoa_replay_method` included, and a refusal there
marks a stale entry. Nothing is run twice: a prerun of an operation that
composes `HAVE` would advance `prem_counter` and skip premise numbers
between the live run and replay. A `run` that may leave such a variable
instantiates it itself.

`msg` names the operation and the shared variables, in the singular or the
plural as `_gate_rejection` does, says that the operation's result leaves
each of them in more than one of its subgoals and that this is not allowed,
and names no remedy, because the variable may come from the operation's
argument or, for an operation with no input gate, from the goal:
`Apply left the schematic variable ?y in more than one of the subgoals it produced. A schematic variable may be left in at most one subgoal, so this step is rejected.`
— with several variables, `the schematic variables ?x, ?y`. It reaches the
agent through the step's one failure channel (§8): a `Leaf` passes it
through unchanged, and for the block bases the base's
`_beginning_opr_err_msgs` frames it, as it frames the built-in
`Could not eliminate the residual schematic variables …`; a plugin that
knows which of its arguments fixes the variable adds that in this hook.

The check applies to every user operation and needs no declaration of the
Python base: a `Leaf` derives at most one subgoal, as every built-in `Leaf`
does — a second one would have no `NEXT` to reach it and would be left to
the block's end — and a `StdBlock` that is not a `SubgoalMaker` opens one
goal, so for both the check holds vacuously, and it bites only for a
`SubgoalMaker`, as the built-in probe does. An operation that leaves
several subgoals, a proof method among them, is a `SubgoalMaker`.
`UserNode` enforces the one-subgoal rule of a `Leaf` in Python, in its
`_execute_opr` after the operation ran: it reads `new_subgoals_count` of
the resulting state, which for a `USER` step is never `None` and counts
the same derived subgoals the ML check used (§2), and when it exceeds one
fails the step with an error naming the operation, raised as the
`IsabelleError` that `Leaf._refresh_me_alone` turns into the step's
failure.

On the input side, a `SubgoalMaker` plugin class refuses a goal sequent
that has schematic variables anywhere in it, sibling goals included,
through `Branch`'s gate, shared as one module-level helper
`_refuse_schematic_goal(state, op_name)` next to `_gate_rejection` which
`Branch.can_operate_on_schematic_goal` and
`UserNode.can_operate_on_schematic_goal` call: a block opener such as
`CONSIDER` copies the whole sequent into every case, while its `Goals`
message lists only the leading goal. A `StdBlock` plugin class that is not
a `SubgoalMaker` keeps `Node`'s default, as `Have`, `Suffices`, `Obtain`
and `SetupRewriting` do.

**A user operation that opens a block** leaves the stack in the shape its
Python base closes (`datatype frame`, `library/proof.ML`). The operation of
a `StdBlock` plugin class that is not a `SubgoalMaker` opens one block the
way `gen_HAVE'` does: the new
goal's `HHF` frame over `ENDBLK T_END`, over a `MAGIC` whose continuation
pushes back the frame the operation popped; `StdBlock`'s `END` then closes
it. Composing `HAVE`, `SUFFICES` or `OBTAIN` produces this shape; composing
`CASE_SPLIT`, `INDUCT` or a multi-clause `CONSIDER` does not — under
`strict_end`, which AoA sets, `END` refuses an `ENDBLK T_NXT`, and over a
bare `MAGIC` `END` runs on the enclosing frame. A `SubgoalMaker` plugin
class's operation that opens a block leaves the shape `GoalContainer`
closes: `NEXT` closes every child but the last, so each child but the last
is an `HHF` over `ENDBLK T_NXT` over a `MAGIC`; the last child needs no
closing command — an `HHF` over a bare `MAGIC`, as `CASES'` leaves
(`CASE_SPLIT`, `INDUCT`), or the restored frame itself, as a multi-clause
`CONSIDER` leaves (`Branch`). A `T_END` block under a `SubgoalMaker` is
never closed.

### 4.2 A user task

A `Task` subclass registered with `@aoa_task(name)`, whose constructor
takes the decoded payload. The two built-in tasks are registered the same
way, `@aoa_task("usual")` and `@aoa_task("learning")`, and the dispatch in
`IsaMini_AoA` (`toplevel.py`) is one table lookup. `@aoa_task` makes the
duplicate-name and abstractness checks of §4.1.

The interface (`task.py`) is two async hooks, each building one whole
prompt: `system_prompt(role, session)` returns the system prompt, or
`None` to send none, and `initial_prompt(role, session, has_system)`
returns the initial message, `has_system` saying whether a system prompt
is sent. The session appends the tactic block (TACTIC_DESIGN.md §7.3) to
the system prompt, or to the initial message when there is none; a task
includes it in neither. `role`, in every hook, is the role of the session
the prompt is built for, `Role_Major` or `Role_Worker` (`Session` passes
its own role). An interaction fork has no system prompt or initial
message of its own: it is sent the system prompt of the session that
launched it, and sees that session's initial message only inside a
copied conversation.

A task that wants the framework's prompts with its own words in them
derives from `StdTask`, which implements both hooks and offers two text
hooks, `task_system(role)` and `task_initial(role, has_system)`, both
returning `""` by default:

```python
@aoa_task("termination")
class TerminationTask(StdTask):
    def __init__(self, payload):
        self.names, self.equations = payload
    def task_initial(self, role, has_system):
        if not isinstance(role, Role_Major):
            return ""
        return <the equations, ending in a blank line>
```

The text of either hook is whole lines, each ending in `"\n"`, inserted
as it is: the framework adds no separator around it, and `""` gives the
prompt without a task. `task_system`'s text continues the first paragraph
of the role's body of the system prompt and the framework's paragraph
break follows, so the text ends in a single `"\n"`, not a blank line.
`task_initial`'s text opens the initial message and the framework's text
follows directly, so a text that forms a section of its own ends in a
blank line, as `LearningTask`'s Isar block does.

The two text hooks receive no session: their text can name no tool (the
spelling is the driver's, through `Session.tool_name`) and no feature
gated per call (`write_memory`, experience retrieval). A task that needs
a value of the session overrides a whole hook of `StdTask` and adds to
`super()`'s result. In the initial message the text goes at
`task_initial`'s place, under the same whitespace rule:

```python
    async def initial_prompt(self, role, session, has_system):
        return <text> + await super().initial_prompt(role, session, has_system)
```

In the system prompt, text can only go before or after
`await super().system_prompt(role, session)` (which is `str | None`):
text after it follows the tool list and precedes the tactic block, no
text reaches the place after the first paragraph, and the whitespace
where the two texts meet is the task's own. Such a hook uses the session
it is given, never the session of the running context (an interaction
fork's system prompt is built from the session that launched it, in the
fork's context), and does not store it on the task (one task serves
every session of the call, and the hooks run concurrently). As the hooks'
docstrings say, the system prompt may depend only on the task, the role
and the session's configuration, since the session may build it again at
any time; the initial message is memoized and resent at compaction and
restart. A task whose prompts are not the framework's at all derives from
`Task` and implements the two hooks itself.

---

## 5. One AoA call

### 5.1 The task and the selection

A task is one shape, built-ins included:

```sml
type task = {name : string, payload : MessagePackBinIO.Pack.raw_packer}
val usual    : task                      (* name "usual",    payload packString "" *)
val learning : string -> task            (* name "learning", payload the Isar proof *)
```

`usual` and `learning` are registered once through `Theory.setup` with no
packages; a user task is registered by its plugin (§1). The payload is
whatever the Python task needs and only the ML caller has — for a
termination task, the function's names and equations — written by the
caller with the packers, so it is already in wire form; the call sends
`(name, payload)`, and Python decodes the payload and passes it to the
registered class's constructor. The wire is as before; `pack_task` goes.

The active operations of a call are `active_operations thy selection`: the
registered operations with `default = true`, plus those the selection
includes, minus those it excludes; a name the theory does not register is
an error of the call.

The entry points (`agent_server.ML`), each with the selection beside the
task; `hammer_or_AoA` gains `task` as well, having run `usual` implicitly:

```sml
val raw_AoA : {driver: driver, minilang_cfg: MiniLang_Agent.cfg,
               budget: MiniLang_Agent.budget, invocation_id: string, task: task,
               user_operations: user_operation_selection}
           -> Proof.context * thm
           -> (MiniLang_Agent.xcmd list * agent_cost * Phi_Proof_Store.times * string) * thm

val run_AoA : {driver: driver, minilang_cfg: MiniLang_Agent.cfg,
               budget: MiniLang_Agent.budget, invocation_id: string,
               read_store: bool option, write_store: bool option,
               async_mode: Phi_Sledgehammer_Solver.async_mode, task: task,
               user_operations: user_operation_selection}
           -> Proof.context * thm
           -> (MiniLang_Agent.xcmd list * agent_cost * Phi_Proof_Store.times * string) future * thm

val hammer_or_AoA :
     {fact_override: Sledgehammer.fact_override,
      proof_id: Phi_Proof_Store.proof_id option,
      hammer_timeout: Time.time option,
      async_mode: Phi_Sledgehammer_Solver.async_mode,
      read_store: bool option, write_store: bool option,
      task: task,
      user_operations: user_operation_selection}
  -> Proof.context -> thm
  -> string future * thm
```

`hammer_or_aoa_method` — the body of `by aoa` and of `by hammer_or_aoa` —
keeps its signature and passes `usual` and `[]`: a
proof written by hand runs with the resident operations only. Only a
caller in ML selects. An SML record argument is given exactly its declared
fields, so every caller that writes one out changes with it: `AoA_REPL_App`
(`Agent/AoA_REPL/aoa_repl_app.ML`), the caller of the model tests, whose
own wire is unchanged, passes `usual` and `[]`; so do phi-system's
obligation layer (`phi-system/Phi_Logic_Programming_Reasoner/library/reasoners.ML`,
a separate submodule, so a commit there and a bump) and test 24 of
`Test/Test_Proof_Store_Hash_Hit.thy`; `tasks/AoA-learning/learning.ML`
passes `learning isar` and `[]`. `aoa_replay_method` is unchanged (§2).

### 5.2 Start of the call

In `raw_AoA`, after the gate and before the agent starts:

1. `active_operations thy selection`, and `the_task thy (#name task)`,
   each raising on a name no registration carries; the `#python_packages`
   of each registration and of the task's answer, deduplicated;
2. `Remote_Procedure_Calling.load` those packages after `IsaMini.AoA`, so
   the imports — hence the registrations and their checks — happen before
   the call;
3. build the active operations' callbacks from their `callbacks env`,
   `env` holding the call's state table and, as its `config`, the function
   `current_config` itself — one local function of `raw_AoA` built from
   the replay-mode ref, which `proof_opr_callback` and
   `schematic_vars_of_derived_subgoals_callback` use in place of their
   inline copies — and append them to `aoa_cmd`'s
   `callback` list; a name already in that list, or one
   `Remote_Procedure_Calling.get_global_callback` answers (`log` is one),
   is an error;
4. send, in the `IsaMini.AoA` argument beside the task, the active
   operations' names, in name order (§1).

On the Python side `IsaMini_AoA` builds the call's **operation table**,
`Runtime.operations: dict[str, OperationMeta]` — the built-in operations
and, for each active name, the class `OPERATION_REGISTRY` holds under it,
which must be a `UserNode` — and the call's `Task` from `TASK_REGISTRY`,
into a `Runtime` it builds right after unpacking the argument, before
`_ensure_semantic_db`, `update_interpretations` and the split by driver, so
that §8's failures come first; the `Runtime` reaches the drivers through
`runtime=` and `TestCase.run` through a parameter `ModelTestCase` hands to
`Session(runtime=...)`. `Session.operations` forwards to it, as
`Session.task` does; the planner, workers and interaction forks share it.
`Parse_Nodes` looks names up in the table and, on a miss, passes the
table's names to `ArgumentError_UnknownProofOperation`, which takes the
list as a parameter; `Minilang_State.execute` reads it for tag 21 (§3);
`_tool_schemas_for` reads it to build the call's `edit` schema (§5.3).
`OPERATION_REGISTRY` is only what imports register into; lookups by class
stay on it. No call sees an inactive operation, and two calls in one host
process with different selections do not see each other's.

### 5.3 The `edit` schema of the call

`tools/cc_edit.jsonc` is the base and keeps the built-in operations. The
call's schema is a copy with each active class's `construct_schema` placed
under `$defs/<name>` and `{"$ref": "#/$defs/<name>"}` appended to
`$defs/Operation.anyOf`, in the order the names arrived, which is name
order (§1), after the built-in operations, whose order the base fixes. A
`construct_schema` refers to the base's shared definitions — `Thought`,
`LongStatement`, `FactByName`, `Proof`, `GivenLater`, … — by `$ref`; a
sub-proof field is named `proof` or `proofs` (§4.1) and refers to `Proof`
or `GivenLater`, never to `Operation` directly.

`_tool_schemas_for` (`mcp_http_server.py`), the one place the advertised
tools are made, builds the call's `edit` schema from `session.operations`
and hands it to `transform_tool_schema` and, through `tool_schemas`, to the
providers, as it already swaps `query`'s schema on
`session.enable_read_memory`; `_TOOL_SCHEMAS["edit"]` keeps its description
and annotations but carries no schema. The advertised schema and
`Parse_Nodes` read the same table, so they cannot disagree, and a fork,
sharing the table, advertises the same tool list as its parent.

Each provider derives its form from the schema `_tool_schemas_for` hands
it, a pure function of it, per call: `OpenAIBase._strict_schema` is
`_strictify_schema(_flatten_edit_schema(schema))`,
`DeepSeekProvider._strict_schema` is `_flatten_edit_schema_deepseek(schema)`,
Gemini's `format_tools` is `_flatten_edit_schema(schema)`, Codex's
`transform_tool_schema` is
`_merge_edit_operations_schema(_flatten_edit_schema(schema))`. The module
constants `_cc_edit_schema_flat`, `_cc_edit_schema_codex`,
`_cc_edit_schema_deepseek_cache` and `_deepseek_edit_schema` go, so no
provider can reach for a form that predates the call; each flattening
checks its own output with `_assert_no_refs` at its end.
`_flatten_edit_schema` resolves a sub-proof field by what it refers to —
a `$ref` to `Proof` becomes the flat proof form — while
`_flatten_edit_schema_deepseek` drops a sub-proof field by its key name,
`proof` or `proofs`; hence the naming convention of §4.1, which a plugin
keeps by hand (§7), since nothing checks it. Codex's merged form drops every
operation's `description`, the built-in ones included; a plugin's is lost
there too.

---

## 6. Where

| piece | file |
| --- | --- |
| `config` and its parts | `Agent/agent_config.ML` (new), structure `MiniLang_Agent_Config` |
| registration (`register_user_operation`, `register_task`), `env`, the lookups `the_operation` and `the_task`, which raise the absence texts, `active_operations`, `user_operation_selection`, `task` | `Agent/agent_plugin.ML` (new), structure `MiniLang_Agent_Plugin` |
| `USER`, the interpreter branch and its check, `read_method_text`, the exported checks | `Agent/agent.ML` |
| `derived_subgoals_of`: its block case without a `Goals` message, its stack-shrink case, its contract comment naming the new caller | `library/proof.ML` |
| the one codec over `MessagePackBinIO`, the `USER` branch's decode error, the in-memory streams | `Agent/agent_packer.ML` (functor collapsed), `Test/Test_Agent_Packer_Recorded_Proof.thy` |
| `pack_opt`, tag 21, the start of the call with `current_config`, the entry points, `usual` and `learning` | `Agent/agent_server.ML` |
| `mk_callback` re-raising whatever escapes its read | `Isabelle_RPC/Tools/RPC.ML` |
| the callers passing `usual` and `[]` / `learning isar` and `[]` | `Agent/AoA_REPL/aoa_repl_app.ML`, `Test/Test_Proof_Store_Hash_Hit.thy`, `tasks/AoA-learning/learning.ML`, `phi-system/Phi_Logic_Programming_Reasoner/library/reasoners.ML` (separate submodule) |
| `UserNode` (with `can_operate_on_schematic_goal`, `_check_registration`, the one-subgoal rule of a `Leaf`, the default `unpack_own_message`), `TASK_REGISTRY`, `@aoa_task`, the decorator checks (the two refusals they share in `check_name_and_abstractness`), `Runtime.operations` and `Session.operations`, the running operation's class passed to `unpack_message` in `Minilang_State.execute`, `ArgumentError_UnknownProofOperation`, `_refuse_schematic_goal`, the `SubgoalMaker` default `_ending_opr_err_msgs` | `model.py`, `task.py`, `helper.py` |
| the base schema's loading, shared by `model.py` and `mcp_http_server.py` | `IsaMini/AoA/edit_schema.py` |
| `_tool_schemas_for` building the call's `edit` schema, `_TOOL_SCHEMAS["edit"]` without a schema, `_flatten_edit_schema`, `_merge_edit_operations_schema` | `mcp_http_server.py` |
| the derived forms as pure functions | `driver_openai_api.py`, `driver_gemini.py`, `driver_codex.py` |
| start of the call, the `Runtime` | `toplevel.py` (`IsaMini_AoA`), `test.py` |

---

## 7. What the plugin author owes

- `name` equal on both halves, within the operation-name grammar of the
  schema (a CamelCase identifier, as the built-in names), unique across
  every plugin one host process loads, built-in names included;
- `pack_arg` and `unpack_arg` inverse to each other, and `payload()`
  readable by `unpack_arg`;
- `unpack_arg` reading every layout an earlier release wrote, through `||`
  alternatives, with a hand-packed blob of each retired layout in the
  plugin's tests, as `Test_Agent_Packer_Recorded_Proof.thy` keeps; a blob
  that no longer decodes is a stale entry, and with the gate closed the
  batch build fails on it (§2);
- `pack_message` answering `SOME` for each message its run reports and
  its node reads;
- a `run` that opens a block of several cases forwards first the `Goals`
  message of the step that opened the block, listing every case as
  `CASE_SPLIT` reports it, since `derived_subgoals_of` reads the cases from
  the first `Goals` (§4.1); a `Leaf` derives at most one subgoal (§4.1);
- a block opened in the stack shape its base closes (§4.1);
- a sub-proof field named `proof` or `proofs` (a list of them), and no
  other field so named, at any depth (§4.1): `_flatten_edit_schema_deepseek`
  drops fields by these names, and a sub-proof field under another name
  that refers to `Proof` makes it recurse without bound (§5.3); a field
  named `simplify` gets DeepSeek's " Most cases: true." appended to its
  description;
- text the agent wrote read through `MiniLang_Agent`'s readers (§1), and
  its execution bounded in time, as the sample's `Apply` is (§1);
- every optional field reading its empty value and `null` as absent, since
  the strict derived forms make every field present;
- every `description` in `construct_schema`: it is the agent's whole
  knowledge of the operation beyond the field names, except under Codex
  (§5.3).

---

## 8. Failures

At import, as §4.1 lists, which the start of a call reports under the
package name. At the start of a call, each ending the call with a message
that names what failed — the package, the operation, the task or the
callback — and the reason; no plugin is skipped quietly:

- a `python_packages` entry that does not import;
- a selected name no registration carries, or a task name none carries;
- an active name under which `OPERATION_REGISTRY` holds no class, or a
  class that is not a `UserNode`; a task name under which `TASK_REGISTRY`
  holds no class;
- a callback name already in `aoa_cmd`'s list or held by a global callback.

An argument `unpack_arg` cannot read, or a `USER` name no registration
carries, fails inside `IsaMini.proof_opr`'s argument read, before any
operation runs: it fails no step but ends the call with the error naming
the operation (§2), and in replay it marks a stale entry. A step fails,
through the one channel every operation uses (§1), when its `run` raises,
when its derived subgoals share a schematic variable, or when a `Leaf`
derives more than one subgoal (§4.1). The texts of all of these are
agent-visible or user-visible and are approved like every other AoA text.
The approved texts (2026-10-08), besides those quoted in §2 and §4.1:

- registration (ML, `agent_plugin.ML`): `User operation "Apply" is registered twice`;
  `User task "usual" is registered twice`;
- the selection and the task at the start of a call (ML): `User operation
  "Nope": no imported theory registers it` (the §2 text, reused for the
  selection and for an unregistered name reached at execution);
  `User task "nope": no imported theory registers it`;
- a callback name clash (ML): `Callback "log" of a user operation: the name
  is already taken`;
- the decorators (Python): `Proof operation "Apply" is already registered by
  <module>.<class>`; `Proof operation "Apply": the class Apply is abstract;
  missing: payload`; `Task "usual" is already registered by <module>.<class>`;
  `Task "abstract": the class Abstract is abstract; missing: initial_prompt,
  system_prompt`;
  and the schema checks, each `User operation "Apply": ` followed by one of
  `its node class defines no construct_schema dict`, `construct_schema is not
  a valid JSON schema: <reason>`, `construct_schema must set
  additionalProperties to false`, `construct_schema must declare
  properties.operation as the const "Apply"`, `the name "Proof" is a
  definition of the base schema`, `construct_schema must not refer to
  #/$defs/Operation; a sub-proof field refers to Proof or GivenLater`,
  `construct_schema refers to #/$defs/X, which the base schema does not define`;
- `read_method_text` (ML, `agent.ML`), the failing spot marked as
  `read_term` marks it: `Outer syntax error: (simp, 【parsing fails here】)`
  (Isabelle's own explanation of the outer-syntax failure is dropped);
  `Unexpected text after the tactic: simp【parsing fails here】)`;
  `The tactic text is empty.`; `Undefined tactic: "simps"` (no marker);
- the start of a call (Python, `Runtime` and
  `IsaMini_AoA`): `User operation "Apply": no imported Python package
  registers a node class under this name.`; `User operation "Have": its node
  class Have is not a UserNode.`; `User task "termination": no imported
  Python package registers a task class under this name.`;
- the one-subgoal rule of a `Leaf` (Python, the step's failure): `User
  operation "TwoGoals" left 2 subgoals, but its node class is a Leaf, which
  may leave at most one; the plugin must make it a SubgoalMaker.`;
- the tag-21 bug guard (Python): `BUG: a message of a user operation arrived
  for a built-in step: <data>`.

---

## 9. Tests

A sample plugin — the `Apply` of the running example, `default = true`
(only test theories import it), with one message of its own: the theory
`IsaMini/AoA/Tests/Sample_Plugin.thy` and the package
`IsaMini/AoA/Tests/sample_plugin/` — exercised by:

- model tests (`test.py`, golden YAML) filling an `Apply` step and
  rendering the tree, under a `by aoa` whose theory imports the plugin; the
  message reaches `cls.unpack_own_message`, and an `Induction` step in the
  same call still succeeds;
- a pytest (`test_user_operations.py`): a plugin whose `pack_message`
  answers `SOME` while its class has no decoder fails with the
  `InternalError` naming the operation, the tag-21 default;
- a replay test: the blob `raw_AoA` would store, built by `encode_blob`,
  replayed by `aoa_replay`, so `pack_arg` and `unpack_arg` are shown
  inverse;
- a `StdBlock` sample whose `run` is `MiniLang_Agent.interpret config (HAVE …)`:
  the user operation opens the block, Python's `END` closes it, the step
  succeeds, and the stored proof replays through `aoa_replay`; the same
  sample run on a goal with schematic variables is allowed;
- `active_operations` as a `theory_test`, with no RPC, covering the
  selection errors;
- a schema test (pytest): a `Session` over a `Runtime` whose operations
  include a `Leaf` sample and a `StdBlock` sample whose `proof` field the
  base parses, both defined in `test_user_operations.py`;
  `_tool_schemas_for(session)["edit"]["schema"]` has both branches, so do
  the four derived forms built from it, and all pass `_assert_no_refs`;
  each flattening's own check catches a `construct_schema` carrying `$defs`;
  DeepSeek's and OpenAI's forms keep a plugin field named like a schema
  keyword (`default`, `properties`) and stay valid schemas; DeepSeek's form
  appends its hint to a field named `simplify`; the built-in operations and
  the base schema's `Operation.anyOf` are checked against each other at
  import;
- an argument `unpack_arg` cannot read, as a `theory_test` over the codec
  with a hand-packed blob in place of a plugin whose `payload()` disagrees
  with its `unpack_arg`: the error names the operation and is not
  `protocol error`;
- a `run` that applies `APPLY''` twice: Python receives one `Goals`,
  counting the final result's derived subgoals;
- `Apply` with `(rule trans)` on `a = c` is refused, the text naming
  `Apply` and `?s`, the step shown with the error and the goal unchanged
  (the check raises inside `interpret`, so no state is recorded); then
  `Apply` with `(rule trans[of a b c])` at the same step gives two child
  goals without schematic variables;
- a `SubgoalMaker` sample composing `CONSIDER` on `G1` of a frame
  `[G1, G2]` where `G2` holds `?y`: refused with the `_gate_rejection`
  sentence;
- a `Leaf` sample whose `run` leaves two subgoals and forwards no `Goals`:
  the step fails naming the operation;
- the §4.1 decorator refusals as plain Python import tests; the §8
  refusals of the call's start, one each.
