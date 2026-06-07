theory Test_Induction_ClassifyVars_Filter
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Induction_ClassifyVars_Filter"]]

text \<open>
  The classification offer is restricted to variables that appear in the
  leading goal. \<open>f\<close> is fixed by the lemma but never appears in the goal
  \<open>n + k = k + n\<close>, so it must NOT be offered; only \<open>k\<close> is.
\<close>

lemma
  fixes f :: "nat \<Rightarrow> nat"
  shows "\<forall>(n::nat) (k::nat). n + k = k + n"
  by aoa

end
