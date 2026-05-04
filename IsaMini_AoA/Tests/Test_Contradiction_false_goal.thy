theory Test_Contradiction_false_goal
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Contradiction_false_goal"]]

lemma "False \<Longrightarrow> False"
  by aoa

end
