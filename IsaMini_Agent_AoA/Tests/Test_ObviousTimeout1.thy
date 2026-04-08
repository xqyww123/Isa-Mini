theory Test_ObviousTimeout1
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.ObviousTimeout_explicit"]]

lemma obvious_timeout_test1: "False"
  by   AgentAoA

end
