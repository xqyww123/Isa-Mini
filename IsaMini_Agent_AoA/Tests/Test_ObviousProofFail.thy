theory Test_ObviousProofFail
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.ObviousProofFail"]]

lemma obvious_fail_test: "(x::int) * x \<ge> 0"
  by   AgentAoA

end
