# The automatic Intro decision: hooks, exemptions and the default

Status: design settled 2026-10-17 (the owner's decisions of that day: the
term, the attribute and its grammar, the check texts, the ML names, the
positions, a separate short document; after the first review round, the
hooks and their four decisions; after the second, the precedence: every hook
before every exemption, whatever the scope of each; after the third, the
functor of §5 and the `aconv` hooks of §0). Implemented 2026-10-17 (§5, §6,
§7); the goldens of the three scripted tests approved by the owner on
2026-10-17, the golden of `AutoIntroDecision` with its step 5 on 2026-10-18;
revised 2026-10-18 after the review of the implementation (the
exported surface of `Goal_Positions`, the one Python helper that builds an
automatic Intro, the split segment in §8, the tests of §7).

> References use stable symbol names, never line numbers — line numbers drift.
> Grep for the symbol.

AoA inserts an `Intro` step on its own, before the agent sees a goal,
whenever the goal opens with a quantifier or a premise (`Minilang.need_intro`,
`library/proof.ML`): the **automatic Intro**. The **automatic Intro
decision** is whether to insert it on a given goal. It is made in one place,
`Auto_Intro.decide` (`Agent/agent_auto_intro.ML`), by three layers asked in
order once `need_intro` holds:

1. the **auto-Intro hooks**: ML functions registered in the context, each
   returning a **verdict** — `Intro` or `No_Intro` — or passing to the next
   hook (§2);
2. the **auto-Intro exemptions**: term patterns registered in the Agent Hint
   Registry (`Agent/agent_hint.ML`, structure `Agent_Hint`) with the goal
   hints' grammar, checks and matching walk (`docs/GOAL_HINTS.md`); a goal
   matching one has the verdict `No_Intro` (§3, §4);
3. the default, `Intro`.

Every hook is asked before every exemption, whatever the scope each was
declared in (decided 2026-10-17): ML can always tell a goal exactly, a
pattern cannot, so a hook's verdict is the stronger statement. A goal left
without its automatic Intro is shown to the agent as it stands, with its
binders and premises in place; the agent's own `Intro` on it works as on any
goal. Nothing is printed for the decision.

Running example throughout: the two proof obligations of a function
definition. After

```isabelle
function sum_upto :: "nat ⇒ nat ⇒ nat" where
  "sum_upto i N = (if N < i then 0 else i + sum_upto (Suc i) N)"
```

pattern completeness is the goal `⋀P x. (⋀i N. x = (i, N) ⟹ P) ⟹ P`
(`mk_completeness`, `HOL/Tools/Function/function_core.ML`), and
`termination` opens the goal printed `All sum_upto_dom`: the term
`All (λx. accp sum_upto_rel x)` (`prepare_termination_proof`,
`HOL/Tools/Function/function.ML`; `sum_upto_dom` abbreviates
`accp sum_upto_rel`). Both goals open with a binder, so AoA inserts its
automatic Intro on both, and that breaks the method each goal is meant for.
`pat_completeness` reads the cases from the subgoal's own premises
(`Logic.strip_horn` in `pat_completeness.ML`); the automatic Intro has moved
them into the context and left the goal `P`, so it finds none and fails.
`relation` and `size_change` (`relation.ML`) resolve the goal against the
function package's stored rule, whose conclusion is literally
`All sum_upto_dom`; on `sum_upto_dom x` they do not apply. In both cases the
agent, told to use that method, fails at step 2 and does not find the way
out, which is to delete AoA's own step first.

The termination goal can be exempted by a pattern:

```isabelle
declare [[aoa_no_auto_intro whole_prop "Wellfounded.accp _ _"]]
```

The completeness goal cannot: its shape lies in its premises, which the
walk never visits (§4), and its conclusion is a bound variable, which only
`_` matches. A hook keeps it. The caller declares the hook for this one call
and holds the call's goal, so the hook compares with `aconv` (decided
2026-10-17):

```sml
Auto_Intro.add_hook ("pattern completeness", fn _ => fn g =>
  if g aconv goal then SOME Auto_Intro.No_Intro else NONE)
```

It answers `No_Intro` on exactly that goal and passes on every other. The
completeness call also carries the compatibility goals
(`mk_compat_proof_obligations`, `function_core.ML`): one per unordered pair
of equations, the diagonal included, so for `sum_upto` one goal,
`⋀i N ia Na. (i, N) = (ia, Na) ⟹ (if N < i then 0 else i + sum_upto_sumC (Suc i, N))
= (if Na < ia then 0 else ia + sum_upto_sumC (Suc ia, Na))`, over the
package's tupled constant `sum_upto_sumC` (`analyze_eqs` in `mutual.ML`,
`define_function` in `function_core.ML`). They are further top-level goals
of the same AoA call, in the same context. With an `aconv` hook exactly the
declared goal is kept: the compatibility goals, and the subgoals the method
leaves — the recursive-call subgoal of `relation` (§1) — keep their automatic
Intro. This holds as long as the goal reaches the decision as the caller
built it; for the function package's goals, which the other segments of the
preprocessing leave alone, that is as long as the split segment has not run
on the call (§8). An exemption's unit is a position (§4), so it also keeps a goal
derived from the exempted one that still carries the pattern at a
proposition position, such as the goal `classical` derives from the
termination goal; that is why a caller may prefer an `aconv` hook for the
termination goal too. TAT's `Define` is to declare, on the proof context of
each of its two AoA calls, what gives the termination goal, or the
completeness goal, the verdict `No_Intro` and leaves every other goal of the
call its automatic Intro, told by the call's task and, on the termination
goal, by a goal hint — a change to
`Theory-Agent-over-Trees/docs/node_classes/DEFINE.md` §7 that follows this
one (§6).

---

## 1. The decision

```sml
val verdict_of : Proof.context -> term -> verdict
  (* the first verdict of the three layers on a leading goal *)
val decide : Minilang.state -> bool
  (* whether AoA inserts its automatic Intro on the state's leading goal *)
```

`decide s` is false when the state has no leading goal; otherwise it is
`Minilang.need_intro` of the leading sequent, and `verdict_of ctxt goal =
Intro`, where `goal` is the term `Minilang.leading_goal_data s` gives — the
same term `need_intro` inspects and the goal hints are matched on — and
`ctxt` is `Minilang.context_of s`, the state's own context, where the hooks
and exemptions declared for it are read: those of the theory, of a locale,
of a proof context, and those TAT declares with `Context.proof_map` on the
proof context of one AoA call, exactly as its goal hints and tactic
whitelist are read there. `verdict_of` asks the hooks in their order (§2) and
takes the first verdict; with none, `No_Intro` when
`Agent_Hint.exempt_from_auto_intro ctxt goal` holds, else `Intro`. The layers
are asked only once `need_intro` holds: with nothing to introduce there is
nothing to decide.

**Where it runs.** Every automatic Intro AoA inserts is decided by one
question to ML: `Minilang_State.decide_auto_intro()` (`IsaMini/AoA/model.py`),
the callback `IsaMini.decide_auto_intro` (`Agent/agent_server.ML`), whose
body is `Auto_Intro.decide`. Until now that method and callback were named
`need_intro` and answered the shape test; they are renamed because their
meaning changes, so that `need_intro` keeps one meaning everywhere, the shape
test (§5). The Python side asks it in one function,
`NonLeaf_Node._should_inject_leading_intro`, which decides for a goal and the
body that follows it: the decision, then, when the body already holds an
`Intro` or an `Induction`, no automatic Intro, except for a body that opens
with an `Induction` on a leading bound variable, which still gets one; the
Induction pre-check (`IsaMini.induction_target_hits_leading_binder`) is
consulted only after the decision has answered true, so a goal left without
its automatic Intro never reaches it. With no body, the function is the
decision alone. It is reached only through
`NonLeaf_Node._make_automatic_intro`, the one way an automatic Intro is
built: it asks, clones the state, marks the node `_auto_injected` and records
it in `auto_intro_nodes`; the five insertion points each keep their own
precondition and place the node it returns:

- `GoalNode._refresh_me_alone`, at a `GoalNode`'s first refresh with no body.
  This covers every `GoalNode`: the main goal's, a case of a `Branch`,
  `CaseSplit` or `Induction`, and a subgoal derived by a `Tactic` or
  `InferenceRule` — which is where the subgoals of `relation` arrive: the
  recursive-call subgoal (`⋀i N. ¬ N < i ⟹ ((Suc i, N), i, N) ∈ …`) gets its
  automatic Intro as before unless a hook or an exemption gives it the
  verdict `No_Intro`, and the `wf` subgoal opens with no binder and gets none;
- `GoalNode._refresh_me_alone`, with the subgoal body a `SubgoalMaker` hands
  to its `GoalNode` (`_pending_proof`);
- `StdBlock._attach_proof` with a body, the `proof` given to a block that
  calls it with `auto_intro` (`Have`, `SetupRewriting`);
- `StdBlock._attach_proof` without a body, when such a block is given none;
- `_auto_Intro_after_child`, the step after a child whose resulting goal
  opens with a binder, when no `Intro` or `Induction` follows among the later
  siblings and, if the child is the last, the block is still opening.

None of the insertion points gives a goal whose verdict is `No_Intro` an
automatic Intro. In particular AoA inserts no Intro before an `Induction` on
such a goal either: an `Induction` on a leading bound variable of it needs
the agent's own `Intro` before it, as on any goal whose bound variables were
not introduced, and `[Intro, Induction y]` works. Beyond the rename and the
helper, Python behaviour is unchanged.

`MiniLang_Agent.check_need_intro` (`Agent/agent.ML`) stays what its name
says, the shape test `Minilang.need_intro` on the leading sequent, and the
Induction pre-check keeps guarding on it, so its documented "true iff the
target mentions a not-yet-introduced leading binder" stays true. The agent's
own `Intro` never asks the decision: `resolve_intro_state` (`Agent/agent.ML`)
and `INTRO''` (`library/proof.ML`) call `Minilang.need_intro` directly.

**Only at insertion.** The decision is read only when AoA decides whether to
insert an automatic Intro. The step it inserts is recorded as an ordinary
`INTRO` op, and replay (`aoa_replay_method`, `Proof_Store_AoA.replay_record`)
interprets the recorded ops in ML without consulting hooks or exemptions.
So a stored proof replays the same with or without them, the proof store key
(`Hasher.all_goals`) needs no part for them, and TAT's proof check and the
emitted `by aoa`, which replay in a context without the call's declarations,
are unaffected — as for the tactic whitelist (`docs/TACTIC_DESIGN.md` §0).
An automatic Intro already in the tree, inserted before an edit gave its
goal the verdict `No_Intro`, is an ordinary Intro step whenever it runs
again, as any automatic Intro is once inserted (the agent is told it may
delete it); `Node._has_considered_auto_intro` is untouched.

**When nothing is registered.** With no hook and both exemption nets empty,
`verdict_of` is `Intro` without walking the goal, and `decide` is
`need_intro`: a theory declaring nothing sees AoA behave byte for byte as
before.

---

## 2. Hooks

```sml
datatype verdict = Intro | No_Intro
type hook = Proof.context -> term -> verdict option
val add_hook : string * hook -> Context.generic -> Context.generic
val hooks : Proof.context -> (string * hook) list   (* in the order asked *)
```

A hook is an ML function of the state's context and the leading goal, the
term `Minilang.leading_goal_data` gives, with its `⋀`, `⟹` and `Trueprop`
structure as it stands (no normalisation); it returns `SOME Intro`, `SOME
No_Intro`, or `NONE` to pass. A hook sees the goal's binders as the goal's
producer built them: the termination goal is `All (λx. accp sum_upto_rel
x)`, while a goal a rewriting step produced may carry an eta-contracted `All
P`; a hook that looks under a quantifier handles both forms, as the walk's
binder rule does (`docs/GOAL_HINTS.md` §2.1). A hook that compares with
`aconv` needs the caller's own term: the printed form of the termination
goal, `All sum_upto_dom`, reads back eta-contracted as `All (accp
sum_upto_rel)`, which is not `aconv` to the goal as `termination` opens it.

**Order.** Hooks live in `Generic_Data` as a list under their serials, and
`hooks` lists them in the order they are asked. Along one line of
declarations the most recently declared hook is asked first; a hook declared
on a proof context — by `Context.proof_map`, as TAT declares for one call —
is asked before the hooks it inherits from its theory, so the inner scope
decides first. At a theory merge the union is taken with the serial as each
hook's identity (`Library.merge`), and the hooks only a later import carries
come before those of an earlier import: when hooks of independent theories
disagree on a goal, the order of the `imports` list decides. Serial order
cannot be the rule there, because theories that load in parallel draw their
serials in an order that depends on scheduling. The name is what `hooks`
lists, for a reader inspecting a context, as a simplifier solver's name is;
the serial is the identity, so the same declaration reached through two
imports is one hook, and a name may repeat.

**Precedence over exemptions.** Every hook, whatever its scope, is asked
before every exemption, whatever its scope; the inner scope decides first
only among hooks. So a hook's `Intro` overrides every exemption, including
one declared on the proof context of a single call, and a declaration that
is to be beyond any imported hook's reach is itself a hook. `Intro` is the
default, so a hook answers `Intro` only to override the `No_Intro` that a
hook asked after it, or an exemption, would give.

A hook that raises propagates its exception: a hook's failure is a bug of its
author's, surfaces as the error of the operation that asked (an
`IsabelleError` on the Python side), and is never read as a verdict. Hooks
are declared from ML only — `setup ‹Context.theory_map (Auto_Intro.add_hook
…)›` in a theory, `Context.proof_map` on a proof context; an Isar command
taking ML source, in the manner of `simproc_setup`, is not part of this
design (§8).

---

## 3. Exemptions: the declaration

```
declare [[aoa_no_auto_intro clause ...]]
clause   ::= whole_prop patterns | subterm patterns
patterns ::= "pattern" (and "pattern")*
```

The grammar is `aoa_notice_goal`'s without its text (`docs/GOAL_HINTS.md`
§1): at least one clause, each a mandatory keyword and one or more patterns
joined by `and`, clauses of either kind repeated and mixed freely. The
attribute is a `Thm.declaration_attribute` that ignores the (empty) fact. Its
description for `print_attributes`: `exempt the goals matching a pattern from
AoA's automatic Intro`.

Each pattern is read as the goal hints read theirs — in pattern mode, in the
declaring context, at declaration time, then `Envir.beta_eta_contract`ed —
and passes the same three checks (`check_pattern`, one body for both
attributes): a whole_prop pattern's type matches `bool`, the pattern's head
is none of the connectives of the `docs/GOAL_HINTS.md` §2.2 table, and no
free variable is unfixed in the declaring context. The messages are the goal
hints' with their first words changed, approved 2026-10-17:

```
Auto-Intro exemption whole_prop "card _": its type is nat, not bool
Auto-Intro exemption subterm "∀x. _ x": it contains the connective ∀
Auto-Intro exemption whole_prop "a dvd b": a is neither a constant nor fixed here; write _ or ?a for an open position, or import the theory that defines it
```

The second check decides how a termination goal is written: `∀x. accp _ x`
is refused, since a fully applied `∀` is never a position, and the pattern
is `Wellfounded.accp _ _`, which matches at the position the walk opens the
`∀` into.

**Scope.** The registry is `Generic_Data`: an exemption declared at theory
level is visible in every theory importing it, one declared inside a locale
or a proof context (`note [[aoa_no_auto_intro ...]]`) is visible there, and
theory merge takes the union. Declaring a pattern again is accepted and
changes nothing.

**The ML entry.** `Agent_Hint.add_auto_intro_exemption {whole_prop, subterm}
: Context.generic -> Context.generic` declares exemptions from ML, for a
caller holding a context as an ML value. The two lists hold the patterns of
the two clauses as text; each is read, contracted and checked exactly as the
attribute reads and checks it (`auto_intro_exemption_declaration`, the one
body of both, with `read_patterns` shared with `add_goal_hint`). The
attribute is this entry behind the parser.

---

## 4. What an exemption matches

A goal matches when any registered pattern matches at a position of its
leading goal under the walk of `docs/GOAL_HINTS.md` §2: a whole_prop pattern
at the proposition positions (the leaves of the goal's propositional
structure, §2.2), a subterm pattern at the term positions (§2.3),
`Pattern.matches` deciding (§2.4). In particular neither kind is tried on the
premises of a `⟹`, the antecedent of a `⟶` or the domain of a `∀x∈A` in the
propositional structure (decided 2026-10-17: the subterm kind too stays as
the goal hints have it), and a quantifier of the table is opened by the
binder rule, so `whole_prop "Wellfounded.accp _ _"` matches the termination
goal at the position `accp sum_upto_rel x`, in its eta-expanded form as
`termination` opens it and in the eta-contracted form it is printed and read
in.

Two consequences of sharing the positions, both accepted by the owner
(2026-10-17): a pattern cannot name the quantifier it sits under (§3); and
the unit of an exemption is a position, not the whole conclusion, so `∀x. 0
< x ⟶ accp R x` is exempt by the same pattern, since `accp R x` is a
proposition position of it. One word, one meaning, for goal hints and
exemptions alike, and one pattern text can serve both a goal hint and an
exemption. What the walk
cannot express — the running example's completeness goal — is a hook's job.

Nothing is computed when no exemption is registered: the walk is pruned by
the two nets as the goal hints' walk is (`docs/GOAL_HINTS.md` §2.4), and
with both nets empty `exempt_from_auto_intro` is false without walking.

---

## 5. The code

**`Agent/agent_hint.ML`.** The walk of `docs/GOAL_HINTS.md` §2, until now
the body of `goal_hints`, and the pair of nets it walks become two modules
at the top of the file, before `Agent_Hint`, since Poly/ML allows a functor
at top level only (checked 2026-10-17). `Goal_Positions` holds what the
positions are: the two kinds of pattern (`kind`, `Whole_Prop | Subterm`,
named after the positions they are matched at), the connective table with
the roles of its arguments (private to the walk; the declaration check sees
only `connective_symbol`), the binder rule (`open_binder`) and the walk

```sml
fold_positions : Proof.context -> {term_positions : bool} ->
  (bool -> term -> 'a -> 'a) -> term -> 'a -> 'a
```

folding a function over every position with the flag "this node lies in the
propositional structure", over the proposition positions only when
`term_positions` is false. The functor `Goal_Patterns`, over an element type
`T` with its `eq` and `key_of`, builds the whole_prop net and the subterm
net (two `iNet_Collection` instances keyed by `key_of`, the pattern of an
element) and exports only

```sml
add : Goal_Positions.kind -> T -> Context.generic -> Context.generic
fold_matches : Proof.context -> (T -> 'a -> 'a) -> term -> 'a -> 'a
```

the second folding over the elements whose pattern matches — the subterm
net's at every position, the whole_prop net's at the proposition positions,
`Pattern.matches` deciding — and walking nothing when both nets are empty.
The nets stay inside the functor, so a goal is only ever matched with the
key its elements were filed under. `Agent_Hint` applies it twice:
`Goal_Hint_Patterns` (`term * goal_hint`, equal when serial and pattern
agree, keyed by the pattern) and `Exemption_Patterns` (`term`, `aconv`, the
identity: an exemption is its pattern). `goal_hints` folds the hints into an
`Inttab` by serial; `exempt_from_auto_intro : Proof.context -> term -> bool`
folds `K (K true)` into `false`. `check_pattern` takes the
declaration's name for its message; `add_exemption`,
`auto_intro_exemption_declaration`, `read_patterns`,
`add_auto_intro_exemption` and the attribute `aoa_no_auto_intro` follow the
goal hints' shapes (§3). Its comments say what the functions compute and
which layer they serve — a match is the verdict `No_Intro` in the
exemptions' layer of `Auto_Intro.verdict_of` — and leave the precedence to
§2 and the `AUTO_INTRO` signature.

**`Agent/agent_auto_intro.ML`, new**, structure `Auto_Intro`: the `verdict`
and `hook` types, the hooks' `Generic_Data`, `add_hook`, `hooks`,
`verdict_of` and `decide` (§1, §2). Loaded by `Agent/Minilang_AoA.thy` right
after `agent_hint.ML`, before `agent.ML`; only `agent_server.ML` calls it.

**`Agent/agent_server.ML`.** The callback `IsaMini.need_intro` becomes
`IsaMini.decide_auto_intro`: its argument the state id alone
(`unpackString`), its body `Auto_Intro.decide (get_state state_id)`. Nothing
else changes; in particular the Induction pre-check callback keeps its guard
on `MiniLang_Agent.check_need_intro`.

**`IsaMini/AoA/model.py`.** `Minilang_State.need_intro(consider_conj)`
becomes `Minilang_State.decide_auto_intro()`: the argument goes, since every
caller passed `False` and the ML side ignored it, and the docstring says
what the method answers — whether AoA inserts its automatic Intro on the
leading goal: the goal opens with a quantifier or a premise, and the
automatic Intro decision (hooks, exemptions, default) says `Intro`. The
insertion points of §1 build their node through
`NonLeaf_Node._make_automatic_intro`, which replaced five copies of the same
block (ask, clone the state, construct the `Intro` with `_auto_injected`,
record it in `auto_intro_nodes`); `_should_inject_leading_intro` moves next
to it, on `NonLeaf_Node`, and its docstring says that the Induction loosening
applies only once the decision has answered true. The docstring of
`StdBlock._attach_proof` names its two callers, `Have` and `SetupRewriting`;
the comment at the `CaseSplit` probe in `test.py` that names the method takes
the new name. The bare name `auto_intro` is not used for the method:
`model.py` already uses it as the boolean flag of `_refresh_me_alone` and
`_attach_proof`.

---

## 6. Changes

ML
- `Agent/agent_hint.ML` (§5). Its header comment names the fourth kind of
  entry and `Auto_Intro.verdict_of` as what reads it.
- `Agent/agent_auto_intro.ML`, new (§5); `Agent/Minilang_AoA.thy` loads it.
- `Agent/agent_server.ML`: the callback `IsaMini.decide_auto_intro` (§5).

Python
- `IsaMini/AoA/model.py`: `Minilang_State.decide_auto_intro`; the helper
  `NonLeaf_Node._make_automatic_intro` at the five insertion points;
  `_should_inject_leading_intro` moved to `NonLeaf_Node`; the three changed
  docstrings and the helper's new one (§5); `IsaMini/AoA/test.py`: the
  comment at the `CaseSplit` probe.

Tests (§7)
- `Tests/User_Operation_Test_Base.thy`: `state_of_term` and `state_of`, a
  Minilang state on a goal given as a term or as text, moved from
  `Tests/Tactic_Replay_Test.thy` and `Tests/User_Operation_Interpret_Test.thy`
  into `User_Operation_Test`, which those two theories then use.
- `Tests/Auto_Intro_Decision_Test.thy`, registered as
  `theory_test("AutoIntroDecision_Minilang", ...)` in `test.py`.
- `Tests/Test_AutoIntroDecision.thy`, `Tests/Test_AutoIntroRelation.thy` and
  `Tests/Test_AutoIntroPatCompleteness.thy` with their `@model_test` cases
  `AutoIntroDecision`, `AutoIntroRelation` and `AutoIntroPatCompleteness` in
  `test.py` (the last two with `isolated_db=True`, since their fixtures
  declare a tactic whitelist) and their goldens.

Documentation
- `docs/GOAL_HINTS.md` §2.1: the sentence "Before AoA shows a goal it
  applies an `Intro` step whenever `need_intro` holds" gains "and the
  automatic Intro decision says so (`docs/AUTO_INTRO_DECISION.md`)"; the
  rationale after it is unchanged, since a goal left without its automatic
  Intro is a goal on which the step has not run. §3's sketch of the registry
  shows the application of the functor `Goal_Patterns` (§5).
- `docs/DEVELOP.md` and the AoA `CLAUDE.md` file map: the `agent_hint.ML` row
  names `aoa_no_auto_intro`, this document and the tests; a row for
  `agent_auto_intro.ML`.

Dependent change, in Theory-Agent-over-Trees (after this one)
- This change lands first and does nothing until a hook or an exemption is
  declared. TAT's `Define` then declares, on the proof context of each of its
  two AoA calls, what gives the termination goal, or the completeness goal,
  the verdict `No_Intro` and leaves every other goal of the call its
  automatic Intro — a hook, or for termination the exemption pattern —
  through the ML entries above, beside the goal hint and the tactic
  whitelist it already declares there (`TAT_Proof_Obligation.ML`,
  `declared`). Which, and the wording of the goal hints it declares beside
  them, are designed in `DEFINE.md` §7 and are the owner's to word where the
  agent sees them. That design must account for the split segment (§8): set
  off by a large compatibility goal, it can rewrite the completeness goal
  before the decision sees it, and an `aconv` hook then passes.
- TAT's scripted termination test,
  `test_a_termination_proof_is_constructed_by_a_scripted_agent_checked_and_emitted`,
  drops its deletion of step 1 and the two assertions around it, fills step 1
  with `relation` directly, and asserts that the first print shows no
  `operation: Intro` under the main goal; its assertion on the derived
  subgoals (the recursive-call subgoal's automatic Intro at `1.2.2`) stays.
  That test is the test of the integration: the ML entries inside a real
  TAT call. The acceptance tests of the motivating need are AoA's own
  `AutoIntroRelation` and `AutoIntroPatCompleteness` (§7). TAT itself has no
  scripted completeness case: under `function (sequential)` it closes pattern
  completeness with `pat_completeness auto`, and the obligation reaches AoA
  only when that fails, which no example in its suite does.

---

## 7. Tests

**The decision, in ML**: `Auto_Intro_Decision_Test.thy`, importing
`User_Operation_Test_Base` for `assert`, `fails_with`, `declared` and
`state_of_term`, in the shape of `Goal_Hints_Test.thy`:
nothing is declared at top level; each case builds its context by applying
the attribute from source text, or `add_hook` and `add_auto_intro_exemption`
from ML, and calls `Auto_Intro.verdict_of` on a term — read in that context,
or taken from the function package — or `Auto_Intro.decide` on a Minilang
state made with `state_of_term`. Every goal of the running example comes
from the package, none is copied by hand: the completeness and compatibility
goals from `Function.function_cmd` on a throwaway local theory, before the
`function` command, while the name is still free (premises 1 and 2 of its
goal state); the termination goal, `All (λx. accp sum_upto_rel x)`, from
`Function.termination NONE` after the definition, whose termination the
theory leaves open for that; the `wf` subgoal and the recursive-call subgoal
from `Function_Relation.relation_infer_tac` on that goal state; the goal
`classical` derives from the completeness goal by `resolve_tac` on
`classical`. The printed form `All sum_upto_dom`, which reads eta-contracted,
is a case of its own.
- With nothing declared, every goal has the verdict `Intro`.
- With `whole_prop "Wellfounded.accp _ _"`: the termination goal, in both
  forms, and `∀x. accp R x` have `No_Intro`; the two subgoals `relation`
  derives have `Intro`; with either kind of the pattern, `∀x. 0 <
  x ⟶ accp R x` and `⋀x. 0 < x ⟹ accp R x` have `No_Intro`, and `∀x. accp R
  x ⟶ 0 < x`, `⋀x. accp R x ⟹ 0 < x` and `∀x∈{y. accp R y}. 0 < x` have
  `Intro`: what Intro would turn into a hypothesis is never visited; `f
  (accp R 0) = c` and `¬ accp R 0` have `No_Intro` by the subterm kind and
  `Intro` by the whole_prop kind; `(∀x. accp R x) ∧ c` has `No_Intro` by the
  whole_prop kind.
- An exemption is no goal hint (`goal_hints` yields nothing in its context)
  and a goal hint with the same pattern is no exemption.
- The three declaration checks with the texts of §3; the grammar: no
  arguments, a text where a clause should start, a pattern without a keyword
  (all "Bad arguments"), a keyword without its patterns ("Outer syntax
  error"); a mixed declaration with `and` accepted. The ML entry gives the
  same verdicts and the same check messages.
- Hooks, the running example's: a hook declared for one call holds that
  call's goal and compares with `aconv`. The completeness goal has `Intro`
  with no hook and `No_Intro` with its hook; the hook passes on the goal
  `classical` derives from it (`⋀P x. (⋀i N. x = (i, N) ⟹ P) ⟹ ¬P ⟹ P`),
  on the compatibility goal, on the termination goal and on a goal
  concluding in a Pure equation (`⋀x::nat. x + 0 ≡ x`), each of which has
  `Intro`, and nothing raises. The termination goal has `No_Intro` with its
  own hook, which passes on the goal's printed form, not `aconv` to it (§2),
  and on the recursive-call subgoal. A passing hook (`K (K NONE)`) changes
  no verdict; a hook answering `Intro` gives `Intro` on the termination goal
  whether declared before or after the exemption — the precedence of §2; two
  hooks answering differently are asked most recently declared first, and
  `hooks` lists them in that order; a hook declared on the proof context is
  asked before, and listed before, one declared on the theory; at a theory
  merge in memory (`Theory.begin_theory`, the idiom of
  `User_Operation_Registry_Test.thy`: a base theory with a passing hook, two
  children each declaring one hook, joined in both orders) the hooks only the
  later import carries come first and the shared one is listed once, so the
  order of the imports decides the verdict; a hook that raises `ERROR "boom"`
  makes `verdict_of` raise it.
- `decide` on a state: true on the termination goal with nothing declared,
  false under the exemption and under its hook; false on the `wf` subgoal
  with nothing declared, the `need_intro` gate, since the goal has no binder,
  and still false with a hook answering `Intro` and with a raising hook, which
  is therefore never asked: the gate comes before the layers; true on the
  recursive-call subgoal; true on the completeness goal with nothing declared
  and false under its hook. The premise of an `aconv` hook:
  the leading goal of a state made on each package goal is `aconv` to that
  goal, so a hook holding the caller's term sees that term.

**The behaviour, scripted** (`@model_test`, each with its own fixture and
golden; the goldens are auto-written on the first run, drafts for the owner
to approve before commit, the rule of the AoA `CLAUDE.md`).

`AutoIntroDecision` (`Test_AutoIntroDecision.thy`) runs the three layers
through a real AoA call: a hook answering `Intro` on any goal that mentions
`Suc`, declared on the theory (`setup ‹Context.theory_map
(Auto_Intro.add_hook …)›`); the exemption `whole_prop "0 ≤ (_::nat)"`,
declared on the proof context of the one call by `using [[aoa_no_auto_intro
…]]` before `by aoa`, the scope TAT declares in; and the lemma `∀x::nat. 0 ≤
x`. Each step names the layer and the §1 insertion point it exercises:
0. The first print: the main goal's `GoalNode` has no child — no automatic
   Intro, the exemption — and its footer asks for step 1
   (`GoalNode._refresh_me_alone` with no body).
1. A `Have` stating `∀y::nat. 0 < y + 1`: no layer answers, the default
   inserts the automatic Intro at `1.1` (`StdBlock._attach_proof` without a
   body).
2. A `Have` stating `∀y::nat. 0 ≤ y`: the exemption, no child, footer asking
   for `2.1`.
3. A `Have` stating `∀y::nat. 0 ≤ Suc y`: the theory's hook answers `Intro`
   over the proof context's exemption, automatic Intro at `3.1`.
4. A `Have` stating `∀y::nat. 0 ≤ y` submitted with `"proof": [{"operation":
   "Obvious", "facts": []}]`, the shape `GoalHintsSuppliedProof` uses: its
   body is that `Obvious` alone, no Intro before it (`StdBlock._attach_proof`
   with a body).
5. A `Have` stating `∀y::nat. 0 ≤ y` submitted with a body that is an
   `Induction` on `y` alone: no automatic Intro before it either, so the
   `Induction` on the still bound `y` fails as it is shown; the agent's own
   `Intro` inserted before it, at `5.0A`, repairs the step: the `Induction`
   opens the case `0`, whose goal `0 ≤ 0` asks for its proof, and the case
   `Suc`, whose goal is `True` and needs no step. This pins that the
   Induction loosening of `_should_inject_leading_intro` applies only once
   the decision has answered true.
   After each of steps 1 to 5, no Intro follows the `Have` under the main
   goal (`_auto_Intro_after_child`).
6. The agent's own `Intro` at step 6 on the main goal, binding `x`:
   committed, the pending goal `0 ≤ x`.
7. `Obvious` at `1.2`, `2.1`, `3.2`, `5.1.0.1` and `7` closes everything:
   `unfinished: 0`.

`AutoIntroRelation` (`Test_AutoIntroRelation.thy`, `isolated_db=True`) is
the motivating need end to end: the fixture defines `sum_upto`, whitelists
`relation` (`AoA_tactics add: relation ‹…›`, the interpretation test data),
declares the exemption, and proves `termination sum_upto` by `aoa`. The first
print shows no child under the main goal; `Tactic` with `relation` and the
arguments `"measure (λ(i, N). N + 1 - i)"` at step 1 is committed; the print
then shows no child under the `wf` subgoal and an automatic Intro under the
recursive-call subgoal; `Obvious` closes both; `unfinished: 0`.

`AutoIntroPatCompleteness` (`Test_AutoIntroPatCompleteness.thy`,
`isolated_db=True`) is the running example itself: the fixture reads the
completeness goal of `function sum_upto` from the package on a throwaway
local theory, declares with `setup` the hook holding that goal, whitelists
`pat_completeness`, and then defines `sum_upto` by `function … by aoa`. The
first print shows the two top-level goals of the call: the completeness goal
`goal1` with no child and the compatibility goal `goal2` with its automatic
Intro at `goal2.1`; `Tactic` with `pat_completeness` at `goal1.1` closes the
completeness goal; `Obvious` at `goal2.2` closes the compatibility goal;
`unfinished: 0`. This is where the hook's motivating use is shown.

§1's "byte for byte as before" rests on the code: with no hook and both nets
empty, `verdict_of` is `Intro` without a walk and `decide` is `need_intro`.
Its check is the regression set run against unchanged goldens:
`GoalHints_Minilang`, `GoalHintsDelivery` and `GoalHintsSuppliedProof`, whose
code path now runs through `fold_matches` and the parameterised
`check_pattern`; `Tactic1`, `AutoIntroQ7Skip`, `AutoIntroQ7Inject`,
`SpliceAutoIntro`, `Induction_AutoIntroBoundVar` and `MultiGoalQuickview`,
whose goals open with a binder and so exercise `decide` through the renamed
callback at each insertion point; and the two theory tests that moved to the
shared `state_of`, `TacticReplay_Minilang` and
`UserOperationInterpret_Minilang`.

---

## 8. Not in scope

Only the leading goal is given to hooks and matched by exemptions; hypotheses
and fixed variables are not. Neither a hook nor an exemption carries a text,
and nothing is shown for the decision; what the agent should do with a goal
left without its automatic Intro is said by what the caller shows the agent
beside the declaration: the call's task text or a whitelisted tactic's
interpretation, and a goal hint where a pattern picks the goal out, as one
does the termination goal.
The connective table and the walk are the goal hints' and change only there.
The decision is read only where AoA inserts its automatic Intro into the
proof tree: the preprocessing `raw_AoA` (`Agent/agent_server.ML`) applies
before `Minilang.INIT` does not consult it, and its segments may change a
goal before the decision sees it. Two of them act across the goals of a call:
`merge_segment` atomizes and conjoins the goals that share a schematic
variable; and when the largest goal of a call exceeds
`preprocess_size_threshold` (`split_race` in `Agent/preprocess.ML` takes the
maximum over all goals), the split segment
(`Goal_Preprocess.preprocess_split_recorded`, a timed race of `auto`,
`clarsimp` and `custom_split_tac`) runs on every goal of the call, so a small
goal a hook or an exemption is meant to keep may be rewritten, or closed,
because another goal of the same call is large. A caller that must hand the
agent a goal exactly as it stands puts the configuration option
`AoA_auto_split` (`Agent/preprocess.ML`, true by default) to false on the
call's context: the segment then answers `NO_SPLIT` whatever the goals' size
and records `""`, so a replay skips it too; TAT's `Define` does so on both of
its calls (`DEFINE.md` §7). `Tests/Auto_Split_Option_Test.thy` pins it.
An Isar command declaring a hook from ML source is left until someone needs
one. Which goals TAT's `Define` keeps as they stand, and the goal hints it
words beside that, are TAT's (`DEFINE.md` §7).
