theory Test_SubtreeStats
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.SubtreeStats"]]

lemma t1: "(x::int) * x \<ge> 0"
  by   aoa

end
