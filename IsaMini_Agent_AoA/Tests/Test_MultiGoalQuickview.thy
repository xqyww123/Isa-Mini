theory Test_MultiGoalQuickview
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.MultiGoalQuickview"]]

lemma
  assumes "P" "Q" "R"
  shows "P" and "Q" and "R"
  by  AgentAoA

end
