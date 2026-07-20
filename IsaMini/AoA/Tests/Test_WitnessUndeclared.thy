theory Test_WitnessUndeclared
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.WitnessUndeclared"]]

lemma witness_undeclared_test: "\<exists>f :: nat \<Rightarrow> nat. f 0 = f 0"
  by  aoa

end
