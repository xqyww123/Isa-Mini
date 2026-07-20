theory Test_Define_AutoProvedRefuse
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Define_AutoProvedRefuse"]]

lemma define_autoproved_test: "\<exists>f :: nat \<Rightarrow> nat. f 0 = 0"
  by  aoa

end
