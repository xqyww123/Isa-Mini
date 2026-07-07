theory Test_WriteMemoryGate
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.WriteMemoryGate"]]

lemma t1: "(1::real) \<le> 2"
  by   aoa

end
