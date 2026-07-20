theory Test_WorkerErrIdLeak_BlockClosed
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.WorkerErrIdLeak_BlockClosed"]]

lemma t1: "(x::int) * x \<ge> 0"
  by aoa

end
