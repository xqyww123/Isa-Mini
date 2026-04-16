theory Consumes_Missing_Fact_Test
  imports Main
begin

text \<open>
  Test: what happens when an induction rule with @{attribute consumes} \<open>= 1\<close>
  is applied without providing the expected major-premise fact.

  @{thm int_le_induct} has the shape:
    \<open>\<lbrakk> i \<le> k;  P k;  \<And>i. \<lbrakk>i \<le> k; P i\<rbrakk> \<Longrightarrow> P (i - 1) \<rbrakk> \<Longrightarrow> P i\<close>
  with \<open>[consumes 1]\<close>, meaning the first premise \<open>i \<le> k\<close> is normally
  discharged by a fact supplied via \<open>using\<close>.

  Below we call \<open>induction rule: int_le_induct\<close> \<^emph>\<open>without\<close> any \<open>using\<close> fact,
  so the \<open>i \<le> k\<close> premise is never consumed.
\<close>

section \<open>A: structured proof --- the undischarged premise becomes a subgoal\<close>

lemma
  fixes i k :: int
  assumes le: "i \<le> k"
  shows "i + k \<ge> 2 * i"
proof (induction i rule: int_le_induct)
  \<comment> \<open>Without \<open>using le\<close>, the major premise \<open>i \<le> k\<close> is NOT consumed.
      Isabelle creates it as an extra proof obligation.\<close>
  show "i \<le> k" by (rule le)   \<comment> \<open>must discharge it manually\<close>
next
  case base
  show ?case by simp
next
  case (step i)
  then show ?case by simp
qed

section \<open>B: compare with the correct usage --- \<open>using le\<close> consumes the premise\<close>

lemma
  fixes i k :: int
  assumes le: "i \<le> k"
  shows "i + k \<ge> 2 * i"
  using le
proof (induction i rule: int_le_induct)
  \<comment> \<open>Now \<open>i \<le> k\<close> is consumed; only the case subgoals remain.\<close>
  case base
  show ?case by simp
next
  case (step i)
  then show ?case by simp
qed

section \<open>C: tactic-level demonstration via ML\<close>

ML \<open>
local
  val ctxt = \<^context>

  (* Goal: P (i::int), with i and k free *)
  val goal_ct = \<^cterm>\<open>P (i::int)\<close>
  val st0 = Goal.init goal_ct

  val rule = @{thm int_le_induct}
  val consumes_n = Rule_Cases.get_consumes rule
  val _ = writeln ("int_le_induct consumes = " ^ string_of_int consumes_n)

  (* Apply induction WITHOUT any facts *)
  val results_no_fact =
    Induction.induction_tac ctxt true
      [[SOME (NONE, (\<^term>\<open>i::int\<close>, false))]]  (* induct on i *)
      []          (* no arbitrary *)
      []          (* no taking *)
      (SOME [rule])
      []          (* NO facts --- the consumed premise is not discharged *)
      1 st0
    |> Seq.list_of

  val _ = writeln ("Without using fact: " ^
    string_of_int (length results_no_fact) ^ " result(s)")
  val _ = case results_no_fact of
      [st] => writeln ("  subgoals = " ^ string_of_int (Thm.nprems_of st) ^
                       "\n" ^ Syntax.string_of_term ctxt (Thm.prop_of st))
    | _ => writeln "  (unexpected number of results)"

  (* Apply induction WITH the fact  i \<le> k *)
  val ik_fact = Goal.prove ctxt ["i","k","P"] [\<^prop>\<open>(i::int) \<le> k\<close>]
                  \<^prop>\<open>(i::int) \<le> k\<close> (fn {prems,...} => resolve_tac ctxt prems 1)
  val results_with_fact =
    Induction.induction_tac ctxt true
      [[SOME (NONE, (\<^term>\<open>i::int\<close>, false))]]
      []
      []
      (SOME [rule])
      [ik_fact]   (* provide the major-premise fact *)
      1 st0
    |> Seq.list_of

  val _ = writeln ("With using fact: " ^
    string_of_int (length results_with_fact) ^ " result(s)")
  val _ = case results_with_fact of
      [st] => writeln ("  subgoals = " ^ string_of_int (Thm.nprems_of st) ^
                       "\n" ^ Syntax.string_of_term ctxt (Thm.prop_of st))
    | _ => writeln "  (unexpected number of results)"
in end
\<close>

end
