theory Test_Sqrt2
  imports Complex_Main MathBench_Prover.MathBench_Prover Minilang_AoA.Minilang_AoA
begin
declare [[auto_interpret_for_embedding=false]]

lemma \<open>sqrt(2) \<notin> \<rat>\<close>
  by aoa

inductive even :: \<open>nat \<Rightarrow> bool\<close> where
  \<open>even 0\<close> | \<open>even n \<Longrightarrow> even (Suc (Suc n))\<close>
thm even.induct

end