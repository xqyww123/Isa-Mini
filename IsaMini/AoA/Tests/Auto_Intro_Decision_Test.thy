theory Auto_Intro_Decision_Test
  imports User_Operation_Test_Base
begin

text \<open>
  The automatic Intro decision (docs/AUTO_INTRO_DECISION.md, section 7): the
  three layers on a leading goal, the exemptions over the positions goal hints
  are matched at, the declaration checks, the ML entries and the decision on a
  state. Nothing is declared at top level: each case builds exactly the context
  it names by applying the attribute from source text with \<open>declared\<close>, or a hook
  or exemption from ML, and calls \<open>Auto_Intro.verdict_of\<close> on a term, or
  \<open>Auto_Intro.decide\<close> on a state made with \<open>state_of_term\<close>. Every goal of the
  running example's function definition is taken from the function package:
  the completeness and compatibility goals as \<open>function\<close> opens them, read on a
  throwaway local theory before the definition, while the name is still free;
  the termination goal as \<open>termination\<close> opens it, after the definition, whose
  termination is left open for that; the two subgoals \<open>relation\<close> derives from
  it; the goal \<open>classical\<close> derives from the completeness goal.
\<close>

ML \<open>
(*premise 1 the completeness goal, premise 2 the compatibility goal*)
val sum_upto_function_goals =
  Function.function_cmd {verbose = false}
    [(Binding.name "sum_upto", SOME "nat \<Rightarrow> nat \<Rightarrow> nat", NoSyn)]
    [((Binding.empty_atts, "sum_upto i N = (if N < i then 0 else i + sum_upto (Suc i) N)"), [], [])]
    Function_Common.default_config (Named_Target.theory_init \<^theory>)
  |> Proof.goal |> #goal |> Thm.prems_of
\<close>

function sum_upto :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "sum_upto i N = (if N < i then 0 else i + sum_upto (Suc i) N)"
  by pat_completeness auto

ML \<open>
local
open User_Operation_Test
open Auto_Intro
val declared = declared "aoa_no_auto_intro"

val ctxt0 = \<^context>
val thy = Proof_Context.theory_of ctxt0
(*the variables of the goals given as text, fixed with their types*)
val (_, ctxt) =
  Proof_Context.add_fixes
    (map (fn (x, T) => (Binding.name x, SOME T, NoSyn))
      [("R", \<^typ>\<open>nat \<Rightarrow> nat \<Rightarrow> bool\<close>), ("f", \<^typ>\<open>bool \<Rightarrow> bool\<close>), ("c", \<^typ>\<open>bool\<close>)]) ctxt0

fun with_exemptions ctxt clauses = fold (fn cl => fn c => declared c cl) clauses ctxt
fun with_hooks ctxt hooks = fold (fn h => Context.the_proof o add_hook h o Context.Proof) hooks ctxt

(*the running example's pattern, as each kind*)
val whole_accp = with_exemptions ctxt ["whole_prop \<open>Wellfounded.accp _ _\<close>"]
val sub_accp = with_exemptions ctxt ["subterm \<open>Wellfounded.accp _ _\<close>"]

fun verdict_name Intro = "Intro"
  | verdict_name No_Intro = "No_Intro"
fun expect_term what ctxt t verdict =
  let val actual = verdict_of ctxt t
   in assert (what ^ ": " ^ Syntax.string_of_term ctxt t ^ " has the verdict " ^ verdict_name actual)
        (actual = verdict) end
fun expect what ctxt s verdict = expect_term what ctxt (Syntax.read_prop ctxt s) verdict
fun leading_goal_of s =
  (case Minilang.leading_goal_data s of
    (SOME (_, goal), _) => goal
  | (NONE, _) => error "no leading goal")

(*the goals of the function package*)
val _ = assert "function opens two goals" (length sum_upto_function_goals = 2)
val completeness_goal = nth sum_upto_function_goals 0
val compatibility_goal = nth sum_upto_function_goals 1
(*the termination goal, All (\<lambda>x. accp sum_upto_rel x) (prepare_termination_proof);
  its printed form reads eta-contracted, All (accp sum_upto_rel)*)
val termination_state = Function.termination NONE (Named_Target.theory_init thy)
val termination_goal = Proof.goal termination_state |> #goal |> Thm.prems_of |> hd
val printed_termination_goal = "All sum_upto_dom"
(*the subgoals relation derives: wf of the measure, then the recursive call*)
val relation_subgoals =
  let val {context = lthy, goal, ...} = Proof.goal termination_state
   in Function_Relation.relation_infer_tac lthy
        (Syntax.read_term lthy "measure (\<lambda>(i, N). N + 1 - i)") 1 goal
      |> Seq.hd |> Thm.prems_of
  end
val _ = assert "relation derives two subgoals" (length relation_subgoals = 2)
val wf_subgoal = nth relation_subgoals 0
val recursive_call_subgoal = nth relation_subgoals 1
(*the goal classical derives from the completeness goal: the same with the
  premise \<not> P*)
val classical_goal =
  Goal.init (Thm.cterm_of ctxt completeness_goal)
  |> resolve_tac ctxt @{thms classical} 1 |> Seq.hd |> Thm.prems_of |> hd
in

(*1: the running example, the exemption*)
val _ = expect_term "nothing declared: the default" ctxt termination_goal Intro
val _ = expect_term "nothing declared: the default" ctxt completeness_goal Intro
val _ = expect_term "the termination goal" whole_accp termination_goal No_Intro
val _ = expect "the printed form of the termination goal" whole_accp printed_termination_goal No_Intro
val _ = expect "a termination goal over a fixed relation" whole_accp "\<forall>x. Wellfounded.accp R x" No_Intro
val _ = expect_term "the recursive-call subgoal relation derives" whole_accp recursive_call_subgoal Intro
val _ = expect_term "the wf subgoal relation derives" whole_accp wf_subgoal Intro

(*2: what Intro would turn into a hypothesis is never visited, by either kind*)
val _ = List.app (fn c =>
  (expect "consequent" c "\<forall>x. 0 < x \<longrightarrow> Wellfounded.accp R x" No_Intro;
   expect "antecedent" c "\<forall>x. Wellfounded.accp R x \<longrightarrow> 0 < x" Intro;
   expect "Pure conclusion" c "\<And>x. 0 < x \<Longrightarrow> Wellfounded.accp R x" No_Intro;
   expect "Pure premise" c "\<And>x. Wellfounded.accp R x \<Longrightarrow> 0 < x" Intro;
   expect "the domain of Ball" c "\<forall>x\<in>{y. Wellfounded.accp R y}. 0 < x" Intro))
  [whole_accp, sub_accp]

(*3: whole_prop at the proposition positions, subterm at every term position*)
val _ = expect "a proposition passed as an argument: whole_prop" whole_accp "f (Wellfounded.accp R 0) = c" Intro
val _ = expect "a proposition passed as an argument: subterm" sub_accp "f (Wellfounded.accp R 0) = c" No_Intro
val _ = expect "under a conjunction" whole_accp "(\<forall>x. Wellfounded.accp R x) \<and> c" No_Intro
val _ = expect "under not: whole_prop" whole_accp "\<not> Wellfounded.accp R 0" Intro
val _ = expect "under not: subterm" sub_accp "\<not> Wellfounded.accp R 0" No_Intro

(*4: an exemption is no goal hint, and a goal hint is no exemption*)
val _ = assert "an exemption is no goal hint"
          (null (Agent_Hint.goal_hints whole_accp (Syntax.read_prop whole_accp "\<forall>x. Wellfounded.accp R x")))
val hinted = User_Operation_Test.declared "aoa_notice_goal" ctxt "\<open>t\<close> whole_prop \<open>Wellfounded.accp _ _\<close>"
val _ = expect "a goal hint is no exemption" hinted "\<forall>x. Wellfounded.accp R x" Intro

(*5: the declaration checks, with the approved texts, and the grammar*)
fun refused text clauses = fails_with text (fn () => declared ctxt0 clauses)
val _ = refused "Auto-Intro exemption whole_prop \"card _\": its type is nat, not bool" "whole_prop \<open>card _\<close>"
val _ = refused "Auto-Intro exemption subterm \"\<forall>x. _ x\": it contains the connective \<forall>" "subterm \<open>\<forall>x. _ x\<close>"
val _ = refused ("Auto-Intro exemption whole_prop \"a dvd b\": a is neither a constant nor fixed here; " ^
                 "write _ or ?a for an open position, or import the theory that defines it")
          "whole_prop \<open>a dvd b\<close>"
(*no arguments, a text where a clause should start, a pattern without a keyword,
  a keyword without its patterns*)
val _ = fails_with "Bad arguments" (fn () => declared ctxt0 "")
val _ = fails_with "Bad arguments" (fn () => declared ctxt0 "\<open>a text\<close> whole_prop \<open>_ dvd _\<close>")
val _ = fails_with "Bad arguments" (fn () => declared ctxt0 "\<open>_ dvd _\<close>")
val _ = fails_with "Outer syntax error" (fn () => declared ctxt0 "whole_prop")
(*accepted: clauses of both kinds, `and` continuing a clause*)
val _ = (declared ctxt0 "whole_prop \<open>_ dvd _\<close> and \<open>0 < _\<close> subterm \<open>gcd _ _\<close>"; ())

(*6: the ML entry of the exemptions: the same verdicts and the same checks*)
fun added ctxt clauses = Context.the_proof (Agent_Hint.add_auto_intro_exemption clauses (Context.Proof ctxt))
val ml_whole = added ctxt {whole_prop = ["Wellfounded.accp _ _"], subterm = []}
val _ = expect_term "ML entry: the termination goal" ml_whole termination_goal No_Intro
val _ = expect "ML entry: an antecedent is not visited" ml_whole "\<forall>x. Wellfounded.accp R x \<longrightarrow> 0 < x" Intro
val _ = expect "ML entry: subterm" (added ctxt {whole_prop = [], subterm = ["Wellfounded.accp _ _"]})
          "f (Wellfounded.accp R 0) = c" No_Intro
val _ = fails_with "Auto-Intro exemption whole_prop \"card _\": its type is nat, not bool"
          (fn () => added ctxt0 {whole_prop = ["card _"], subterm = []})

(*7: the hooks, the first layer. The running example's hooks: a hook declared
  for one call holds that call's goal and compares with aconv.*)
fun keeping name goal = (name, fn _ => fn g => if g aconv goal then SOME No_Intro else NONE)
val completeness_hook = keeping "pattern completeness" completeness_goal
val termination_hook = keeping "termination" termination_goal
val passing = ("pass", K (K NONE))
val raising = ("boom", fn _ => fn _ => error "boom")
fun answering name verdict = (name, fn _ => fn _ => SOME verdict)
val hooked = with_hooks ctxt [completeness_hook]
val _ = expect_term "the completeness goal, no hook" ctxt completeness_goal Intro
val _ = expect_term "the completeness goal, its hook" hooked completeness_goal No_Intro
val _ = expect_term "the hook passes on the goal classical derives" hooked classical_goal Intro
val _ = expect_term "the hook passes on the compatibility goal" hooked compatibility_goal Intro
val _ = expect_term "the hook passes on the termination goal" hooked termination_goal Intro
val _ = expect "the hook passes on a Pure equation" hooked "\<And>x::nat. x + 0 \<equiv> x" Intro
val termination_hooked = with_hooks ctxt [termination_hook]
val _ = expect_term "the termination goal, its hook" termination_hooked termination_goal No_Intro
(*the printed form reads eta-contracted and is not aconv to the goal as
  termination opens it: an aconv hook needs the caller's own term*)
val _ = expect "the printed form of the termination goal is another term" termination_hooked
          printed_termination_goal Intro
val _ = expect_term "the hook passes on the recursive-call subgoal" termination_hooked recursive_call_subgoal Intro
val _ = expect_term "the hook passes, the exemption decides" (with_hooks whole_accp [completeness_hook])
          termination_goal No_Intro
val _ = expect_term "a passing hook changes nothing" (with_hooks whole_accp [passing]) termination_goal No_Intro
val _ = expect_term "a passing hook changes nothing" (with_hooks ctxt [passing]) termination_goal Intro
(*every hook is asked before every exemption: Intro from a hook overrides the
  exemption whether the hook was declared after it or before it*)
val _ = expect_term "Intro from a hook declared after the exemption" (with_hooks whole_accp [answering "force" Intro])
          termination_goal Intro
val _ = expect_term "Intro from a hook declared before the exemption"
          (with_exemptions (with_hooks ctxt [answering "force" Intro]) ["whole_prop \<open>Wellfounded.accp _ _\<close>"])
          termination_goal Intro
(*among hooks the most recently declared is asked first*)
val first_no = with_hooks ctxt [answering "a" Intro, answering "b" No_Intro]
val first_yes = with_hooks ctxt [answering "b" No_Intro, answering "a" Intro]
val _ = expect_term "most recent first: No_Intro" first_no termination_goal No_Intro
val _ = expect_term "most recent first: Intro" first_yes termination_goal Intro
val _ = assert "hooks are listed in the order asked" (map #1 (hooks first_no) = ["b", "a"])
val _ = assert "a context without hooks lists none" (null (hooks ctxt))
(*a hook of the proof context is asked before one of the theory*)
val theory_hooked = Proof_Context.init_global (Context.theory_map (add_hook (answering "theory" Intro)) thy)
val both_scopes = with_hooks theory_hooked [answering "proof" No_Intro]
val _ = expect_term "the proof context's hook first" both_scopes termination_goal No_Intro
val _ = assert "the proof context's hook listed first" (map #1 (hooks both_scopes) = ["proof", "theory"])
(*at a theory merge the hooks only a later import carries come first, the
  shared ancestor's once: the order of the imports decides*)
fun begin name parents = Theory.begin_theory (name, Position.none) parents
val thy_base = begin "AID_Base" [thy] |> Context.theory_map (add_hook ("base", K (K NONE)))
val thy_a = begin "AID_A" [thy_base] |> Context.theory_map (add_hook (answering "A" Intro))
val thy_b = begin "AID_B" [thy_base] |> Context.theory_map (add_hook (answering "B" No_Intro))
val ctxt_ab = Proof_Context.init_global (begin "AID_AB" [thy_a, thy_b])
val ctxt_ba = Proof_Context.init_global (begin "AID_BA" [thy_b, thy_a])
val _ = assert "merge: the later import's hook first" (map #1 (hooks ctxt_ab) = ["B", "A", "base"])
val _ = expect_term "merge: the later import decides" ctxt_ab termination_goal No_Intro
val _ = assert "merge: the other order" (map #1 (hooks ctxt_ba) = ["A", "B", "base"])
val _ = expect_term "merge: the other order decides" ctxt_ba termination_goal Intro
(*a hook that raises is a bug and propagates*)
val _ = fails_with "boom" (fn () => verdict_of (with_hooks ctxt [raising]) termination_goal)

(*8: the decision on a state: the need_intro gate and the verdict*)
val _ = assert "decide: the termination goal, nothing declared" (decide (state_of_term ctxt termination_goal))
val _ = assert "decide: the termination goal under the exemption" (not (decide (state_of_term whole_accp termination_goal)))
val _ = assert "decide: the termination goal under its hook" (not (decide (state_of_term termination_hooked termination_goal)))
val _ = assert "decide: the wf subgoal has no binder, nothing to introduce" (not (decide (state_of_term ctxt wf_subgoal)))
(*the gate comes first: with nothing to introduce no layer is asked*)
val _ = assert "decide: the wf subgoal, a hook answering Intro"
          (not (decide (state_of_term (with_hooks ctxt [answering "force" Intro]) wf_subgoal)))
val _ = assert "decide: the wf subgoal, a raising hook is not asked"
          (not (decide (state_of_term (with_hooks ctxt [raising]) wf_subgoal)))
val _ = assert "decide: the recursive-call subgoal, nothing declared" (decide (state_of_term ctxt recursive_call_subgoal))
val _ = assert "decide: the completeness goal, nothing declared" (decide (state_of_term ctxt completeness_goal))
val _ = assert "decide: the completeness goal under its hook" (not (decide (state_of_term hooked completeness_goal)))
(*the premise of an aconv hook: the leading goal of a state on a goal is that
  goal, as the caller holds it*)
val _ = List.app (fn (what, g) => assert ("INIT keeps " ^ what ^ " as it is") (leading_goal_of (state_of_term ctxt g) aconv g))
  [("the termination goal", termination_goal), ("the completeness goal", completeness_goal),
   ("the compatibility goal", compatibility_goal)]

val _ = writeln "ALL PASS: Auto_Intro_Decision_Test"
end
\<close>

end
