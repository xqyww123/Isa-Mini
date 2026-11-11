theory Test_AutoIntroPatCompleteness
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.AutoIntroPatCompleteness"]]

(* docs/AUTO_INTRO_DECISION.md section 7: the running example's completeness
   goal is kept as it stands by a hook holding that call's goal, so
   `pat_completeness` applies at step 1; the compatibility goal of the same
   call keeps its automatic Intro. The hook is declared here on the theory,
   where TAT declares it on the call's proof context. The interpretation is
   test data. *)
declare [[AoA_tactics add: pat_completeness \<open>prove a pattern-completeness goal by case analysis on the constructors\<close> shown_in: prompt]]

ML \<open>
(*the completeness goal as `function` opens it, read on a throwaway local
  theory while the name is still free*)
val sum_upto_completeness_goal =
  Function.function_cmd {verbose = false}
    [(Binding.name "sum_upto", SOME "nat \<Rightarrow> nat \<Rightarrow> nat", NoSyn)]
    [((Binding.empty_atts, "sum_upto i N = (if N < i then 0 else i + sum_upto (Suc i) N)"), [], [])]
    Function_Common.default_config (Named_Target.theory_init \<^theory>)
  |> Proof.goal |> #goal |> Thm.prems_of |> hd
\<close>

setup \<open>Context.theory_map (Auto_Intro.add_hook ("pattern completeness", fn _ => fn goal =>
  if goal aconv sum_upto_completeness_goal then SOME Auto_Intro.No_Intro else NONE))\<close>

function sum_upto :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "sum_upto i N = (if N < i then 0 else i + sum_upto (Suc i) N)"
  by aoa

end
