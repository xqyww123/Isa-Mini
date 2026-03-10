theory Test_Witness2
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Witness2"]]

lemma t2: "P = Q" for P :: bool
  by  AgentAoA

end
