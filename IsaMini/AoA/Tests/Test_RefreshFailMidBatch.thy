theory Test_RefreshFailMidBatch
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.RefreshFailMidBatch"]]

lemma t1: "(x::int) = x + 1"
  by aoa

end
