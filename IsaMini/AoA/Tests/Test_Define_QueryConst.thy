theory Test_Define_QueryConst
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.Define_QueryConst"]]

lemma "\<exists>f :: nat \<Rightarrow> nat. f 2 = 4"
  by aoa

end
