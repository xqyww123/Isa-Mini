theory Test_WitnessUndeclared
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.WitnessUndeclared"]]

lemma witness_undeclared_test: "\<exists>f :: nat \<Rightarrow> nat. f 0 = f 0"
  by  aoa

end
