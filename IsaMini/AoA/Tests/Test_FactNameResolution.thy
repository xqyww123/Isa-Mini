theory Test_FactNameResolution
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.FactNameResolution"]]

lemma
  fixes x :: "nat"
  assumes h: "x > 2"
  shows "x > 0"
  by  aoa

end
