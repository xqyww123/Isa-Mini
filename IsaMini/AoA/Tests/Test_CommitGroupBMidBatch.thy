theory Test_CommitGroupBMidBatch
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.CommitGroupBMidBatch"]]

lemma t1: "(x::int) = x + 1"
  by aoa

end
