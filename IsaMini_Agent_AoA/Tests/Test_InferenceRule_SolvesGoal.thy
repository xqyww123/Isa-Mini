theory Test_InferenceRule_SolvesGoal
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.InferenceRuleSolvesGoal"]]

lemma "(a :: nat) = a"
  by aoa

end
