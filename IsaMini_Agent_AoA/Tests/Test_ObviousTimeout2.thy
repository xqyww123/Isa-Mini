theory Test_ObviousTimeout2
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.ObviousTimeout_default"]]

lemma obvious_timeout_test2: "True"
  by AgentAoA

end
