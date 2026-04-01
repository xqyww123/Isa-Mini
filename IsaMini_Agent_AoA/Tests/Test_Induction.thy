theory Test_Induction
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Induction"]]

lemma t4: "rev (rev l) = l"
  by  AgentAoA

end
