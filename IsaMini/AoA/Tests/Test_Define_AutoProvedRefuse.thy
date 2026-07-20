theory Test_Define_AutoProvedRefuse
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.Define_AutoProvedRefuse"]]

lemma define_autoproved_test: "\<exists>f :: nat \<Rightarrow> nat. f 0 = 0"
  by  aoa

end
