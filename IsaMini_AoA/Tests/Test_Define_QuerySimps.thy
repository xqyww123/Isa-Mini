theory Test_Define_QuerySimps
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Define_QuerySimps"]]

lemma "\<exists>f :: nat \<Rightarrow> nat. f 2 = 4"
  by aoa

end
