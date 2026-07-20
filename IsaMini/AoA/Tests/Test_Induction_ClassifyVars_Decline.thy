theory Test_Induction_ClassifyVars_Decline
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Induction_ClassifyVars_Decline"]]

text \<open>
  Decline path: when the agent selects none of the offered unclassified
  variables, each stays \<open>fixed\<close> (the same end state as the old silent
  default, but now an explicit choice).
\<close>

lemma "\<forall>(n::nat) (k::nat). n + k = k + n"
  by aoa

end
