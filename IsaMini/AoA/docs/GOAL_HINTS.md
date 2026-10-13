# Goal hints: notices keyed on the shape of a goal

Status: design, settled 2026-10-09 and revised after two reviews, the last
on 2026-10-10; implemented 2026-10-10 in the order of section 9; revised
2026-10-12 after the review of the implementation (the keyword is
mandatory, §1; a fully applied connective of the table is not a position,
§2.2 and §2.3).

> References use stable symbol names, never line numbers — line numbers drift.
> Grep for the symbol.

A **goal hint** is a hand-written text, registered in a theory together with
term patterns, that AoA shows to the agent when a goal the agent is asked to
prove has a conclusion matching one of the patterns. It is the third kind of
entry in the Agent Hint Registry (`Agent/agent_hint.ML`, structure
`Agent_Hint`), beside constant hints and fact hints. Those two fire on what the
agent *writes* (a constant in an authored term, a fact referenced by name);
a goal hint fires on what the agent *sees*. They differ in how they travel:
a constant or fact hint is a message an operation reports, a goal hint is
part of the goal a state carries. All three are rendered as a `notice:`
block shown once per session and again after compaction; a goal hint's
block sits at the end of the footer that asks the agent to prove its goal.

Running example throughout:

```isabelle
declare [[aoa_notice_goal
  "To prove a divisibility `a dvd b`, look for a witness `b = a * k` (`dvd_def`),
   or chain through `dvd_trans`."
  whole_prop "_ dvd _"]]

declare [[aoa_notice_goal
  "`gcd` goals usually go through `gcd_unique_nat` / `gcd_dvd1` / `gcd_dvd2`."
  subterm "gcd _ _"]]
```

With these two in scope, the goal `gcd a b dvd a ∧ 0 < a` shows both texts;
the goal `f (a dvd b) = c` shows neither, and `card {x. gcd x n = 1} = n`
shows only the second.

---

## 1. Declaration

```
declare [[aoa_notice_goal "text" clause ...]]
clause   ::= whole_prop patterns | subterm patterns
patterns ::= "pattern" (and "pattern")*
```

A hint carries one text and at least one clause; a clause starts with its
keyword and carries one or more patterns joined by `and`, and clauses of
either kind may be repeated and mixed. The keyword is never left out
(decided 2026-10-12): a pattern without a keyword, and a second pattern
without `and`, are parse errors rather than silent whole_prop clauses. The
hint fires when any of its patterns matches in its clause's scope (§2).

**`whole_prop` versus `subterm`.** A whole_prop pattern is tried at the
proposition positions (§2.2) — the leaves of the goal's propositional
structure — and must match the whole proposition found there. A subterm
pattern is tried at the term positions (§2.3).

**Parsing.** The attribute is a `Thm.declaration_attribute` that ignores the
(empty) fact, exactly like `aoa_notice_constant`. `whole_prop` and
`subterm` are identifiers read as quasi-keywords with `Args.$$$`; `and`
is a Pure keyword token, which `Parse.embedded` refuses, so a
`Parse.and_list1'` list of patterns ends unambiguously where the next
clause begins. A clause keyword must never be an outer-syntax command word
(`proposition`, `prop` and `term` are, so none of them can serve; checked
with `Keyword.is_command (Thy_Header.get_keywords' ctxt)` in a HOL theory):
Isabelle cuts a theory into command spans at every command word before any
attribute reads its arguments, `[[ ]]` notwithstanding. Once a keyword has
been read the parser is committed to that clause (a cut, `Parse.!!!!`), so
a malformed clause reports a parse error. The hint's serial is allocated
once, when the arguments are parsed, so one declaration is one hint
however many patterns it carries.
Each pattern is read as `Scan.lift (Scan.ahead Parse.embedded)
-- Args.term_pattern`, the idiom of Attrib's `Scan.ahead Args.alt_name --
Args.named_fact`: the token keeps the text the author wrote for the error
messages (a read term cannot be printed back faithfully, since pattern
mode rewrites a `_` under a binder), and `Args.term_pattern` reads the
term in pattern mode, in the declaring context, at declaration time — so
constant names are resolved and fully qualified when the hint is declared,
the same reason the constant attributes use `Args.const`. In pattern mode
`_` is an anonymous schematic variable and `?x` a named one, and types may
be left open; authors write `_` or `?x` for every position they mean to
leave open, since a plain name that is neither a constant nor fixed in the
declaring context is refused (the third check below). Pattern mode expands
abbreviations, so the checks see `_ ≠ 0` as `¬ (_ = 0)` and `_ ∉ _` as
`¬ (_ ∈ _)`; both are accepted (`¬` is a leaf, §2.2). Each pattern is
replaced by its `Envir.beta_eta_contract` as soon as it is read; the three
checks run on that term, and that term is stored: it is the net key (§3)
and the form `Pattern.first_order_match` requires.

**Checked at declaration.** Three checks, each on one pattern; a failure
quotes the offending pattern as the author wrote it, after its clause's
keyword.
- A whole_prop pattern's type must match `bool`: `Sign.typ_match` against
  `HOLogic.boolT`, which admits `bool` itself and a type variable whose
  sort `bool` belongs to, and refuses `?'a::gcd` (no `gcd` instance of
  `bool`) as it refuses `nat`. The message prints the pattern's type with
  its sorts (`Syntax.string_of_typ` under `show_sorts`), so a sort failure
  shows its reason; a concrete type prints plainly. A subterm pattern may
  have any type.
- The stored pattern's head (`Term.head_of`) must be none of the
  connectives of the §2.2 table — `∧`, `∨`, `⟶`, `⟷`, `∀`, `∃`, `∃!`,
  `Ball`, `Bex`, Pure `⟹`, `⋀`, `Trueprop` — whatever the number of
  arguments, a partial application such as `(∧) _` included. One test on
  the head suffices: a pattern is tried only at a position, and a fully
  applied connective of the table is never one (§2.2), so a pattern headed
  by a connective could fire only where the connective stands alone — as
  the bare constant, or as a partial application such as `(∧) a` in
  `map ((∧) a) xs` — and such patterns are refused all the same. A
  connective inside a pattern with any other head — `subterm "card {x. _ x
  ∧ _ x}"` — is compared by `Pattern.matches` as part of the position the
  pattern is tried at (here the `card` node), so it passes. The connective set is defined once
  in `agent_hint.ML`, each constant paired with the symbol the message
  prints (`HOL.All` with `∀`, `Pure.imp` with `⟹`, ..., written as Isabelle
  symbols so the IDE renders them), and used by the walk's table and by
  this check.
  `HOL.eq` is the connective `⟷` when its argument type, as read, is
  literally `bool`; an equation at an open type `?'a` names one atomic
  equation and passes, as `whole_prop "_"` does: the check is on what the
  pattern spells. Such a pattern fires on equations and never on a
  bi-implication, since a `⟷` node of a goal is not a position (§2.3).
  `¬` is not in the set: the walk does not look through it. The check sees
  the contracted pattern, so a redex cannot hide a connective:
  `(λx. x ∧ _) _` is refused for `∧`.
- No pattern may contain a free variable that is not fixed in the context
  it is read in (`Variable.add_frees`: the free variables not fixed in the
  context). At theory level no
  goal variable is related to the declaration, and a misspelled or
  unimported constant name is read as such a variable; either would be
  registered and never fire. Locale parameters and variables introduced by
  `fix` pass.

The texts, approved 2026-10-10 (the keyword re-spelled with them):

```
Goal hint whole_prop "gcd _ _": its type is ?'a::gcd, not bool
Goal hint whole_prop "card _": its type is nat, not bool
Goal hint subterm "∀x. _ x": it contains the connective ∀
Goal hint whole_prop "a dvd b": a is neither a constant nor fixed here; write _ or ?a for an open position, or import the theory that defines it
```

The first two are one template: the keyword, the pattern, its type with
sorts. The third names the pattern's head connective; the fourth the
first such variable. The attribute's description for `print_attributes`:
`register an AoA notice shown when a goal's conclusion matches a pattern`.

**Scope.** The registry is `Generic_Data`, so a hint declared at theory level
is visible in every theory importing it, and a hint declared inside a locale
or a proof context (`note [[aoa_notice_goal ...]]`) is visible there. Theory
merge takes the union.

**Renamed attributes.** The four existing attributes take the same prefix:
`agent_notice_constant` → `aoa_notice_constant`,
`agent_reject_constant` → `aoa_reject_constant`,
`agent_notice` → `aoa_notice`, `agent_reject` → `aoa_reject`, with no
aliases for the old names. ML and Python names (`Agent_Hint`,
`HINT_NOTICE`, `Hint_Notice_Msg`) do not change. Their users are listed in
§6.

---

## 2. What matches

### 2.1 The conclusion

The goal is the leading goal of a Minilang state as shipped to Python
(`Minilang.leading_goal_data`): the term the agent sees after `goal:`. The
root of the walk is its `Envir.beta_norm`, and the walk reaches the
conclusion through the three Pure rows of the §2.2 table: the outer `⋀`
opens its binder by the binder rule below, the outer Pure `⟹` never visits
its premises and continues with its conclusion, and `Trueprop` continues
with its argument. A conclusion that is not a `Trueprop` (a Pure equation,
say) is a leaf of the propositional structure (§2.2), so a proposition
position like any other leaf. No eta step:
`Envir.beta_eta_contract` would turn `∀x. 0 ≤ x` into `All (less_eq 0)`
and remove binders, and none is needed at a position, because
`iNet.match_term` normalises along its own descent and `Pattern.matches`
matches modulo eta. Which positions exist is decided by the binder rule:
the argument of a quantifier of the §2.2 table is opened whether or not it
is eta-contracted, and an eta-contracted argument of any other constant is
not — `card (Collect finite)` has no position `finite X`, `card {X. finite
X}` does.

**The binder rule.** Wherever the walk goes under a binder — the `⋀` and
the quantifiers of the §2.2 table wherever they occur, the abstractions
of §2.3 — it takes the binder's argument `f`, fixes a fresh
variable `x` of `f`'s domain type (`Variable.variant_fixes`), and continues
with `Term.betapply (f, Free x)`. For an abstraction this is its body with
the bound variable replaced, as `Variable.dest_abs` would give; for an
eta-contracted argument such as `less_eq 0` it is `0 ≤ x`. The rule always
succeeds, so the walk never raises, and `Pattern.match` never meets a loose
bound variable.

**What is never visited.** Before AoA shows a goal it applies an `Intro`
step whenever `need_intro` holds (`library/proof.ML`): the premises of a
Pure `⟹`, the antecedent of a `⟶`, and the `x ∈ A` of a `∀x∈A` at the head
of the goal become hypotheses, and hypotheses are not matched (§8). The
hints of a goal must not depend on whether that step has run, nor on
whether the goal sits inside a conjunction where it does not run; so the
walk never visits what `Intro` would turn into a hypothesis: the premises
of a `⟹`, and the antecedent of a `⟶` and the domain `A` of a `∀x∈A`,
that lie in the propositional structure (§2.2), in both clause kinds. A
`⟶` or `∀x∈A` anywhere outside the propositional structure — inside a set
comprehension, an `if` condition, a function argument, or under `¬` — is
never turned into a hypothesis and hides nothing. The domain of `∃x∈A` is visited: membership
must be proved there.

### 2.2 Proposition positions (`whole_prop`)

The goal's **propositional structure** starts at the root. A node of it
whose head is one of the connectives below, applied in full, puts the
listed arguments into the structure, recursively; the table also says what
it leaves unvisited. Every other node of the structure is one of its
leaves, and the leaves are the proposition positions.

| connective | arguments in the structure | not visited |
|---|---|---|
| `⋀x. P` | `P`, by the binder rule | |
| `A ⟹ B` | `B` | `A` |
| `Trueprop A` | `A` | |
| `A ∧ B`, `A ∨ B`, `A ⟷ B` (`HOL.eq` at `bool`) | `A`, `B` | |
| `A ⟶ B` | `B` | `A` |
| `∀x. P`, `∃x. P`, `∃!x. P` | `P`, by the binder rule | |
| `∀x∈A. P` (`Ball`) | `P`, by the binder rule | `A` |
| `∃x∈A. P` (`Bex`) | `P`, by the binder rule; `A` is a term position | |

A fully applied connective of this table is not itself a position, in the
propositional structure or outside it; nor are its head, its partial
applications, or the abstraction a quantifier binds. The walk visits its
arguments only: in the propositional structure each as the table says;
outside it every argument, which lies outside the structure too, the
argument of a binder opened by the binder rule (nothing is left unvisited
there, §2.1). So no pattern is ever tried
against a `⟶` node or the partial application `(⟶) A`, and a
schematic-headed pattern such as `subterm "?f (_ dvd _)"` cannot fire on
`x dvd n ⟶ x ≤ n` through its antecedent: the rule of §2.1 holds by
construction, whatever the pattern.

`¬ A` is a leaf: `whole_prop "_ dvd _"` does not fire on `¬ (a dvd b)`,
`whole_prop "¬ (_ dvd _)"` does, and since `x ≠ 0` is `¬ (x = 0)`,
`whole_prop "_ ≠ 0"` fires on `x ≠ 0` and not on `x = 0`. The table is
fixed; a proposition built with any other constant (`if`, `Let`, a
user-defined connective) is a leaf of the propositional structure. So
`whole_prop "p"` means: what remains to be proved has the form `p`.

### 2.3 Term positions (`subterm`)

The walk starts at the root. At a fully applied connective of the §2.2
table, which is never a term position, it visits the arguments as §2.2
says: in the propositional structure those the table lists, outside it
every argument, the argument of a binder opened by the binder rule. Every
other node it visits is a term position, and below such a node it visits
both sides of an application and, by the binder rule, the body of an
abstraction. So every proposition position is a term position; the head
of a fully applied connective, its partial applications and the
abstraction a quantifier binds are not; and the body of the argument of
every quantifier of the table (`All`, `Ex`, `Ex1`, the predicate argument
of `Ball` and `Bex`) is visited wherever it occurs, including an
eta-contracted one, so `All (less_eq 0)` has the term position `0 ≤ x`,
the same position `All (λx. 0 ≤ x)` has. Types are not visited. `¬` hides nothing here: `subterm "_ dvd _"` fires on
`¬ (a dvd b)`, and on `¬ (a dvd b ⟶ c)`, whose `⟶` lies outside the
propositional structure.

### 2.4 Matching and the walk

A pattern matches a position when `Pattern.matches thy (pattern, subterm)`
holds: higher-order pattern matching with type matching, so `_` and `?x`
match any term of a matching type and a pattern typed `?'a` matches at any
type.

The registry holds two discrimination nets (§3): the whole_prop net and
the subterm net. One recursive walk visits every position of §2.3,
carrying the flag "this node lies in the propositional structure" (§2.2);
every proposition position is one of them by construction, so pruning
changes only which nets are queried, never which hints match. At a fully
applied connective of the table the walk dispatches on the roles of its
arguments — in the propositional structure the table's roles, outside it
every argument visited with the flag false, the argument of a binder
opened by the binder rule — and the node itself is not a position; at
every other node it queries the nets and descends into
both sides of an application or, by the binder rule, the body of an
abstraction. The flag is always tracked, whatever is registered, because
the exclusions depend on it. At every position the walk queries the
subterm net, at proposition positions also the whole_prop net, and
confirms each candidate with `Pattern.matches` (a net keys on term
skeletons, ignores types and repeated variables, and over-approximates).
The walk is pruned by what is registered:

| whole_prop net | subterm net | walk |
|---|---|---|
| empty | empty | none — nothing is computed |
| non-empty | empty | proposition positions only |
| empty | non-empty | every term position, the whole_prop net never queried |
| non-empty | non-empty | every term position |

The result for one goal is the list of hints matched at any position by any
of their clauses, each hint once, in declaration order (by serial). All
hits are reported: hints are independent pieces of an author's knowledge,
and nothing in the system can rank them; the author controls how specific
each pattern is, and the once-per-session rule (§5) bounds the total.

---

## 3. The registry

`Agent_Hint` gains:

```sml
type goal_hint = {serial : serial, text : string}

(* one element per (pattern, hint); a hint with n patterns is n elements *)
structure Whole_Prop_Patterns = iNet_Collection(
  type T = term * goal_hint
  fun eq ((p1, h1), (p2, h2)) = #serial h1 = #serial h2 andalso p1 aconv p2
  val key_of = fst)
structure Subterm_Patterns = iNet_Collection( (* same parameters *) )

val goal_hints : Proof.context -> term -> goal_hint list
  (* the hints of a leading goal, in declaration order; [] when nothing is registered *)
```

`iNet_Collection` (`Performant_Isabelle_ML/library/inet_collection.ML`) is
the existing `Generic_Data` slot over an `iNet` with `add`, `del` and
`iNet.merge eq` for theory merge; `my_object_logic.ML` already uses its thm
specialisation. The key is the pattern, the element carries the hint, so
`iNet.match_term` on a subterm returns the candidate `(pattern, hint)` pairs
directly. The serial is allocated by `serial ()` at declaration; it orders
the output and is the identity the Python side deduplicates on, as the
string `"goal:<serial>"`, in the same `shown_hints` set as the constant
names and `unfold:conditional-definition`.

---

## 4. Where matching runs, and how a hint travels

A goal hint depends only on a state's leading goal and that state's
context, and the leading goal reaches Python through one packer,
`minilang_flat_goal_packer` (`Agent/agent_server.ML`), at two call sites:
the reply of every `IsaMini.proof_opr` and the initial argument of
`IsaMini.AoA`. The hints travel inside that value, the **flat goal**: the
`(items, goal term, count)` the packer already sends.

ML: one function `flat_goal_of : Minilang.state -> flat_goal` in
`agent_server.ML`, with `type flat_goal = (Minilang.items * term *
Agent_Hint.goal_hint list) option * int`, computes, for a state `s`,
`Minilang.leading_goal_data s` and, when there is a leading goal,
`Agent_Hint.goal_hints (Minilang.context_of s) goal` on it (`[]` when there
is none). The `IsaMini.proof_opr` callback calls
it on the new state `s1` inside its `Exn.capture`, and `raw_AoA` calls it
on `s0` for the `IsaMini.AoA` argument; `minilang_flat_goal_packer` only
packs the result. The wire becomes `(1, (items, goal_text, hints), count)`
with `hints` a `(serial, text)` list; the solved form `0` is unchanged.
Nothing touches `minilang_message_packer`, no message kind or tag is added,
and the `IsaMini.AoA` argument keeps its `packTuple12` shape: the hints sit
inside slot 2.

Python: `Minilang_State._unpack_flat_goal` returns `(goal, count, hints)`,
the hints as `Goal_Hint(name = "goal:<serial>", text)` records (a
`NamedTuple`, not a `Message`). `Minilang_State.goal_hints :
list[Goal_Hint]` is assigned in the same statement as `leading_goal`, in
`Minilang_State.execute` and in `Root.__init__`; `reset` clears it with the
goal. `clone` needs no change: its `SKIP`'s reply carries the clone's own
hints. `toplevel.py` passes the unpacked flat goal on as today, so the
`Root` built by `ModelTestCase.run` (`test.py`) receives the initial hints
through `ptree` with no code change, and `test_user_operations.py`'s
literal `0` stays valid (no goal, no hints).

So every `Minilang_State` carries the hints of its own leading goal, by
construction: one wire value, one assignment. They are computed where the
state is produced and with its own context (`Context.Proof ctxt` is where
the registry is read, so locale- and proof-local hints apply). A state is
produced for every operation whether or not it changed the leading goal (a
`Have` leaves the main goal as it was), so the hints of an unchanged goal
are recomputed: the walk is one pass over the conclusion, and the
session-level deduplication (§5) absorbs the repeats. Nothing is computed
when no goal hint is registered.

---

## 5. Delivery to the agent

A goal hint is printed by the footer that asks for its goal's proof, at the
end of that footer, so the agent never has to guess which goal a hint is
about. A block prints that request when `should_I_show_pending_goal()` is
not `None`, in two surfaces. The full print, `StdBlock._print_footer`,
prints one of the three `print_pending_goal` forms: "Unfinished Proof! ...
to provide the proof for the following goal." followed by `pending proof
goal:` and the goal, or "... to provide the proof." with no goal, or "...
to replace it with a proof." The inline view,
`StdBlock._quickview_pending_footer`, prints "Unfinished Proof. Fill step
..." and, only sometimes, a `goal:` line. As the last statement of the
branch where `should_I_show_pending_goal()` is not `None`, after whatever
that branch printed, both call one `Session` helper,
`Session._print_goal_hints(state, indent, file, *, consume)`, on
`self._state_before_ending_`, the state whose leading goal the footer asks
to prove, with the keyword-only `consume` in the shape of
`_emit_pending_hint_notices(indent, file, *, consume)`: `_print_footer`
passes `False`, `_quickview_pending_footer` passes `True`. The hints do not
depend on whether the goal line was printed: `_print_footer` omits it when
`_should_print_footer_pending_goal()` is `False` (a `GoalNode` with no
children, or with only `Have` and `Obtain` children), and
`_quickview_pending_footer` omits it when a `Rewrite` child already printed
the same conclusion or when the goal equals `_prev_pending_goal`, which
`_reset_view_state` does not clear. The helper takes the state's
`goal_hints`, drops those whose `name` is in `Session.shown_hints` or in
the render's own set (below), prints the rest as a `notice:` block at the
footer's indent, and adds their names to `shown_hints` when `consume` is
set. `_consuming_subagent_hints` stays as it is: which kind of render is
running is already fixed by the footer method that calls the helper.

**One printer.** The `notice:` block layout — the header,
`_postprocess_outbound_text`, `- ` at indent+1 and continuation lines at
indent+2 — is extracted from `_emit_pending_hint_notices` into one
`Session` printer, `_print_notice_block(indent, file, texts)`, which both
`_emit_pending_hint_notices` and the helper call. The operation-notice
output stays byte-identical, which the existing hint goldens
(`HintNoticeConst.yml` and siblings) verify.

**Once per render.** A goal hint prints at most once per render, under the
first footer in render order whose goal matches: the names already printed
live in a set on the render's output sink, `MyIO.printed_goal_hints`
(`IsaMini/AoA/helper.py`), and live as long as that sink, the same as its
line counter. Every
production render writes into its own fresh `MyIO` — each driver's
`refresh_YAML`, `_write_quickview`'s scratch sink, `subagent_overall`, the
interaction prompts, `print_string` / `quickview_string`, `log_proof` — so
no entry point has to remember to reset anything; a caller that writes
several renders into one sink gets one set for all of them (§7). Without
this, a non-consuming `proof.yaml` would print the same text under every
matching footer (the k cases of an induction on a divisibility goal, k
times).

Every block that prints the request prints the hints, with no further
case: a `GoalNode` — a case of a `Branch`, a derived subgoal of a rule, the
top-level `GoalNode` of the Root that holds the main goal (id `""` when
there is one, `goal1..goalN` when there are several) — while its proof is
missing or incomplete (a fresh one's `_state_before_ending_` is a clone of
its `ml_state` and carries the same hints); a `Have`-like block in the
single-goal case, where there is no `GoalNode` and the block holds its
subgoal itself. The Root prints no footer of its own: `Root.print` and
`Root.quickview` render the `GlobalEnv` and these `GoalNode`s, and
`Root.opening()` is `False`. A worker's scoped view (`print_proof_scope`
and `quickview_proof_scope` under `Role_Worker`) ends with its target's
footer — `_print_footer` or `_quickview_pending_footer`, or each
obligation `GoalNode`'s own in the multi-goal case — so the worker gets its
target goal's hints there through the same helper.

**When the agent sees it.** The surfaces that print footers and mark hints
shown are the quickviews: the `Outline:` of an `edit` that commits and of a
`delete` (`_write_quickview`), the `Overall:` of every `subagent` response
(`subagent_overall` calls `proof_scope_root.quickview` directly), and the
interaction prompts that call `quickview_proof_scope`. The surfaces that
print footers without marking are the full prints: `proof.yaml`
(`print_proof_scope`, written at session start by `refresh_YAML` and after
every tool call — the initial prompt tells the agent to read it and embeds
no proof render itself) and the `print_string` renders (the archive of a
removed node, the log snapshot). A hint therefore first appears in the
`proof.yaml` or the quickview that follows the goal's creation, and the
initial goal's hints are in the first `proof.yaml`. The system prompt is
not touched.

So a goal hint is shown exactly where the view asks the agent to prove its
goal. A goal whose proof is complete has no such footer and gets no hint;
a goal submitted together with its complete proof never had one; the
state between two steps submitted in one `edit` carries its hints like any
state, and nothing prints them.

Everything else is the existing machinery: a hint shows once per session
(its key enters `shown_hints` on a consuming render), the same hint
matched by a later goal of the same shape is not repeated, and
`_reset_view_state` (compaction, context restart) clears the set so the
next render shows it again. A worker session starts with an empty
`shown_hints` (only an interaction fork copies its parent's), so a worker
sees the hints of its target goal afresh, as today. The text is printed
verbatim through `_postprocess_outbound_text`.

---

## 6. Changes

ML
- `Agent/agent_hint.ML`: rename the four attributes, their `Attrib.setup`
  bindings and the usage comments that name them (§1); add `goal_hint`,
  the connective set, the two `iNet_Collection` instances, the
  `aoa_notice_goal` attribute with its three declaration-time checks and
  the approved texts, the walk of §2 and `goal_hints`.
- `Agent/agent_server.ML`: `flat_goal_of`, called by the `IsaMini.proof_opr`
  callback and by `raw_AoA`; `minilang_flat_goal_packer` packs the hints
  (§4).

Python
- `IsaMini/AoA/model.py`: `Goal_Hint`; `_unpack_flat_goal`;
  `Minilang_State.goal_hints` (assigned in `execute` and `Root.__init__`,
  cleared in `reset`); the `notice:` printer extracted from
  `_emit_pending_hint_notices`; the goal-hint helper and its calls from
  `StdBlock._print_footer` and `StdBlock._quickview_pending_footer` (§5).
- `IsaMini/AoA/helper.py`: the per-render set on `MyIO` (§5).
- `IsaMini/AoA/test.py`: the three `run` annotations of the test cases
  take the new type (`Flat_Goal`, the alias of the flat goal in `model.py`);
  `toplevel.py` is unchanged, it passes the unpacked value on.

Main repository, outside the Isa-Mini submodule
- `tasks/MathBench_Prover/MathBench_Prover.thy` declares
  `agent_reject_constant Rat.of_int` and is imported by thirteen Isa-Mini
  test fixtures: it becomes `aoa_reject_constant`, edited in the same step
  as `agent_hint.ML` and committed in the main-repository commit that
  bumps the submodule. Its git-ignored `MathBench_Prover.unicode.thy` is
  regenerated with `Isabelle_RPC_Host.unicode`, never edited by hand. The
  `MathBench_Prover` heap must then be rebuilt, which waits for the
  owner's build command.
- The inventory scan for the rename, run before and after:
  `/usr/bin/grep -rlIE "agent_(notice|reject)(_constant)?\b"` over the
  repository, leaving out the Isabelle and AFP distributions and `ICSE27*`:
  the ICSE27 snapshot holds same-named copies of `agent_hint.ML` and of the
  five `Test_Hint*.thy` theories, and they are never edited.

Tests
- The five theories under `IsaMini/AoA/Tests/` that declare the renamed
  attributes (`Test_HintNoticeConst`, `Test_HintRejectConst`,
  `Test_HintNoticeFact`, `Test_HintRejectFact`,
  `Test_HintRejectSetupRewriting`).
- `Tests/User_Operation_Test_Base.thy`: `declared` (applying an attribute
  from source text in ML, today local to `Tactic_Declaration_Test.thy`)
  moves into `User_Operation_Test` with the attribute name as a parameter;
  `Tactic_Declaration_Test.thy` calls it from there.
- New (§7): `Tests/Goal_Hints_Test.thy` with its `theory_test` registration
  in `test.py`; `Tests/Test_GoalHintsDelivery.thy` and
  `Tests/Test_GoalHintsSuppliedProof.thy` with their `@model_test` cases in
  `test.py` and their goldens `GoalHintsDelivery.yml` and
  `GoalHintsSuppliedProof.yml`.

Documentation
- `docs/DEVELOP.md` and the AoA `CLAUDE.md` file map name the new files
  and the renamed attributes.

---

## 7. Tests

**Matching, in ML**: `theory_test("GoalHints_Minilang",
"Goal_Hints_Test.thy")`, importing `User_Operation_Test_Base` for `assert`
and `fails_with`. No goal hint is declared at top level: each case builds
exactly the context it names by applying the attribute from source text
with `declared`, and calls `goal_hints` on a term read in that context.
With the running example's two hints:
- `gcd a b dvd a ∧ 0 < a` yields both, in declaration order; `gcd a b ≡
  1`, a conclusion that is not a `Trueprop`, yields the subterm hint;
- `f (a dvd b) = c` yields nothing; with a third hint `subterm "_ dvd _"`
  it yields that hint only: a proposition passed as an argument is a term
  position, not a proposition position;
- `∀x. x ≤ n ⟶ x dvd n` yields the whole_prop hint (binder opened,
  consequent visited); `∀x. x dvd n ⟶ x ≤ n` and `(∀x. x dvd n ⟶ x ≤ n) ∧
  0 < n` do not: an antecedent in the propositional structure is never
  visited, and with `subterm "_ dvd _"` alone `∀x. x dvd n ⟶ x ≤ n` yields
  nothing either;
- `⋀x. x ∈ A ⟹ x dvd n` yields the whole_prop hint; `⋀x. x dvd n ⟹ x ∈ A`
  does not, with the whole_prop hint or with `subterm "_ dvd _"` alone;
- `subterm "?f (_ dvd _)"` and `subterm "?f (_ dvd _) _"` yield nothing on
  `x dvd n ⟶ x ≤ n` and on `¬ (a dvd b ⟶ c)`, whose `⟶` lies outside the
  propositional structure (neither the `⟶` node nor its partial
  application is a position, in the structure or outside it), and the
  first yields its hint on `f (a dvd b) = c`;
- `subterm "λx. x dvd _ ⟶ _"` yields nothing on `∀x. x dvd n ⟶ x ≤ n` and
  on `¬ (∀x. x dvd n ⟶ x ≤ n)`, whose `∀` lies outside the propositional
  structure (the abstraction a quantifier binds is not a position, in the
  structure or outside it), and its hint on `card {x. x dvd n ⟶ x ≤ n} =
  k` (the abstraction of a comprehension is one);
- each remaining row of the §2.2 table, with the whole_prop hint, and the
  other side of each symmetric row: `0 < a ∧ a dvd b`, `0 < a ∨ a dvd b`,
  `a dvd b ∨ 0 < a`, `c ⟷ a dvd b`, `a dvd b ⟷ c`, `∃k. a dvd k`, `∃!k. a
  dvd k` and `∃x∈A. x dvd n` yield it;
- `¬ (a dvd b)` does not yield the whole_prop hint; with
  `whole_prop "¬ (_ dvd _)"` or `subterm "_ dvd _"` it does; with
  `subterm "_ dvd _"`, `¬ (a dvd b ⟶ c)` and `card {x. x dvd n ⟶ x ≤ n} =
  k` yield it, and `card {x. gcd x n = 1 ⟶ x dvd n} = k` yields the
  running example's `subterm "gcd _ _"`: a `⟶` outside the propositional
  structure hides nothing;
- with `whole_prop "_ ≠ 0"`: `x ≠ 0` yields it, `x = 0` does not; with
  `whole_prop "_ = _"`: `gcd a b = 1` yields it (an equation at `nat` is
  one proposition position), `c ⟷ a dvd b` does not (a `⟷` node is not a
  position);
- `∀x::nat. 0 ≤ x` and an eta-contracted `All (less_eq 0)` built in ML
  both yield `whole_prop "0 ≤ _"`; with `subterm "_ ≤ _"`, `All (less_eq
  0)` yields it both in a context holding only that hint and in one that
  also holds a whole_prop hint; under `¬` (a leaf of the propositional
  structure, so the quantifier lies outside it) `¬ (All (less_eq 0))` and
  `¬ (∀x::nat. 0 ≤ x)` yield
  only `subterm "_ ≤ _"` in the context holding both; `∀x∈A. x dvd n`
  yields the whole_prop hint; with `subterm "finite _"`, `card {X. finite
  X}` yields it and `card (Collect finite)` does not;
- with `subterm "_ dvd _"`: `∀x∈{y. y dvd n}. x ≤ n` yields nothing (the
  domain is not visited), `∃x∈{y. y dvd n}. x ≤ n` yields it;
- in a context holding no goal hint, `gcd a b dvd a ∧ 0 < a` yields
  nothing; in a context holding only the whole_prop hint, the cases above
  give their results and `f (a dvd b) = c` yields nothing. (Pruning itself
  is not observable through `goal_hints`; it is a cost, not a result.)
- the net ignores types and repeated variables, `Pattern.matches`
  decides: `whole_prop "(_::int) dvd _"` yields nothing on `a dvd b` at
  `nat` and its hint on `int a dvd int b`; `whole_prop "?x dvd ?x"` yields
  its hint on `a dvd a` and nothing on `a dvd b`;
- one declaration with two patterns, `whole_prop "_ dvd _" and "0 < _"`,
  yields its one hint once on `gcd a b dvd a ∧ 0 < a` and on `0 < a`.

Declaration checks, each with `fails_with` and the approved text:
`whole_prop "card _"` (type, `nat`) and `whole_prop "gcd _ _"` (type,
`?'a::gcd`); `whole_prop "_ ∧ _"`, `subterm "∀x. _ x"`, `whole_prop "_ ⟷
_"`, `whole_prop "(λx. x ∧ _) _"` (after contraction) and `subterm "(∧) _"`
(a partial application) (connective); `whole_prop "a dvd b"` at theory
level and `whole_prop "gdc _ _"` (free variable). Parse errors: a keyword
without its patterns, a pattern without a keyword, a second pattern
without `and` (`subterm "_ dvd _" "_ < _"`), and a text without any
clause. Accepted: `whole_prop "_"` (a type variable matches `bool`),
`whole_prop "_ = _"`, `whole_prop "_ ≠ 0"`, `whole_prop "_ ∉ _"`, `subterm
"card {x. _ x ∧ _ x}"`, and `whole_prop "_ dvd _" and "gcd _ _ = _" subterm
"gcd _ _" and "card _"` — `and` continues the clause it is in and keeps
its kind, since `card _` read as whole_prop would be refused for its type.
In a context where `a` and `b` are fixed, `whole_prop "a dvd b"` is
accepted.

**Delivery, scripted** (`@model_test`, like `HintNoticeConst`, each with
its own `Test_*.thy` and golden). `ModelTestCase.run` hands one `MyIO` to
the whole test body, so every render below goes into its own fresh
`MyIO(io.StringIO())` and is then copied into `file`, the shape of
`_write_quickview` and of test.py's `buf_ps` / `buf_qv`; a render names
its surface: `print_proof_scope` (the full print, non-consuming),
`quickview_proof_scope` (the inline view, consuming) or
`prompts.subagent_overall` (consuming). Every expectation follows from the
rules of §5.

`GoalHintsDelivery`: the two running-example hints and a third,
`subterm "card _"`; the lemma `assumes "0 < a" shows "gcd a b dvd a ∧ 0 <
a"` with `a b :: nat`.
0. The first `print_proof_scope`: the dvd and gcd texts in one `notice:`
   block under the main goal's footer, which prints no goal line (a
   conjunction gets no `Intro` step, so the `GoalNode` has no children).
1. `quickview_proof_scope`: both texts, now consumed.
2. `Have` `a dvd a * b` (provable), then `print_proof_scope`: nothing under
   its footer — the dvd text was consumed in step 1.
3. `Have` `card {a} = 1`, then `print_proof_scope` only: the card text
   under that `Have`'s footer, not under the main goal's. The following
   steps keep to `print_proof_scope`, so that the card text stays unshown
   for the two checks below.
4. Inside that `Have`, a `Branch` on `a < 1`, `a = 1`, `1 < a`, then
   `print_proof_scope`: the card text once, under case `N.1` — the
   exhaustiveness case `N.0`, printed first, is a disjunction that matches
   no hint, and `N.2`, `N.3` follow `N.1` in render order.
5. `subagent_overall` twice: the first shows the card text and marks it,
   the second omits it.
6. `_reset_view_state`, then `print_proof_scope`: every text again, each
   under the first footer in render order whose goal matches — children
   print before their parent's footer, so the dvd text sits under the
   first `Have`'s footer, the card text under case `N.1`, and the gcd text
   under the main goal's footer (which prints no goal line: its children
   are all `Have`s); then `quickview_proof_scope`, in which the unchanged
   goal lines are hidden by `_prev_pending_goal`: the texts still appear
   under the same "Unfinished Proof. Fill step ..." lines and are
   consumed, and a further `print_proof_scope` omits them.
7. Close every pending goal with `Obvious` — the first `Have`, the
   exhaustiveness case `N.0` and the cases `N.1`..`N.3`, then the main goal
   (`gcd_dvd1` and the assumption) — then `_reset_view_state` and
   `print_proof_scope`: nothing.

`GoalHintsSuppliedProof`: a lemma with no matching initial goal, where a
`Have` whose statement is `a dvd a * b` is submitted together with its
`Obvious` proof: nothing is shown on either surface.

Auto-written goldens are drafts for the owner to approve before commit.

---

## 8. Not in scope

Hypotheses and fixed variables are not matched, only the conclusion. The
text is static; nothing of the matched instance is substituted into it.
There is no reject severity for goals: a goal's shape is never the agent's
mistake. The connective table of §2.2 is fixed.

---

## 9. Implementation order

Each step leaves the tree working; the ML steps are checked by restarting
the REPL (a restart loads edited `.ML` from source; `isabelle build` is
never run without the owner's command), the Python steps by
`python -u ../../test_AoA.py -f <name> > <file> 2>&1`, one case at a time.

1. The rename (§1, §6): `agent_hint.ML`, the five test theories,
   `MathBench_Prover.thy` in the main repository, its regenerated
   `.unicode.thy`; the inventory scan before and after. The existing hint
   tests (`HintNoticeConst` and siblings) still pass against their goldens.
   The `MathBench_Prover` heap is stale from here until the owner rebuilds
   it; tests importing it wait for that.
2. `agent_hint.ML`: `goal_hint`, the connective set with its symbols, the
   two collections, the walk, `goal_hints`, the attribute with its three
   checks and the approved texts. `Goal_Hints_Test.thy` (§7, matching and
   declaration checks) passes as a `theory_test`, after `declared` has
   moved into `User_Operation_Test`.
3. `agent_server.ML`: `flat_goal_of`, its two call sites, the packer (§4).
   `model.py`: `Goal_Hint`, `_unpack_flat_goal`, `goal_hints` on
   `Minilang_State`, `Root.__init__`, `reset`, the `Flat_Goal` alias; the
   annotations in `test.py`. Every existing `@model_test` still passes:
   nothing is printed yet.
4. `helper.py`: `MyIO.printed_goal_hints`. `model.py`:
   `_print_notice_block` extracted (the hint goldens prove the output
   unchanged), `_print_goal_hints`, the two footer calls (§5).
5. `Test_GoalHintsDelivery.thy`, `Test_GoalHintsSuppliedProof.thy`, their
   `@model_test` cases (§7); the auto-written goldens go to the owner for
   approval.
6. `docs/DEVELOP.md` and the AoA `CLAUDE.md` file map.
7. One commit in the Isa-Mini submodule and one in the main repository
   that bumps it and carries the `MathBench_Prover.thy` edit; each message
   names the rename.
