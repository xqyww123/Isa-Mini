theory Test_Specialize3
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Specialize3"]]

lemma specialize_test3:
  assumes h1: "P (0::nat)"
  shows "P (0::nat)"
  by  aoa

end
