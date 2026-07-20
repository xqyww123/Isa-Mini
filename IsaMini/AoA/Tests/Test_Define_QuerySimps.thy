theory Test_Define_QuerySimps
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Define_QuerySimps"]]

lemma "\<exists>f :: nat \<Rightarrow> nat. f 2 = 4"
  by aoa

end
