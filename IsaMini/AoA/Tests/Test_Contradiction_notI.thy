theory Test_Contradiction_notI
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Contradiction_notI"]]

lemma contra_notI: "\<not> False"
  by aoa

end
