theory Test_RefreshFailMidBatch
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.RefreshFailMidBatch"]]

lemma t1: "(x::int) = x + 1"
  by aoa

end
