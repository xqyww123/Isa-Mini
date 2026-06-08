theory Test_Induction_MetaIHFact
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Induction_MetaIHFact"]]

lemma
  fixes n :: nat and f :: "nat \<Rightarrow> nat"
  shows "True"
  by aoa

end
