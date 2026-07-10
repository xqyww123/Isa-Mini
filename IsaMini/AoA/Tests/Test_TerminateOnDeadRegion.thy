theory Test_TerminateOnDeadRegion
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.TerminateOnDeadRegion"]]

lemma t1: "(x::int) * x \<ge> 0"
  by aoa

end
