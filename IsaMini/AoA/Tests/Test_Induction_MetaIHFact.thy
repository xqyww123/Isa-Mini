theory Test_Induction_MetaIHFact
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Induction_MetaIHFact"]]

lemma
  fixes n :: nat and f :: "nat \<Rightarrow> nat"
  shows "True"
  by aoa

end
