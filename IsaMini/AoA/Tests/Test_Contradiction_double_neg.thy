theory Test_Contradiction_double_neg
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Contradiction_double_neg"]]

lemma "\<not> \<not> True"
  by aoa

end
