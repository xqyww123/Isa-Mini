theory Test_CommitGroupBMidBatch
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.CommitGroupBMidBatch"]]

lemma t1: "(x::int) = x + 1"
  by aoa

end
