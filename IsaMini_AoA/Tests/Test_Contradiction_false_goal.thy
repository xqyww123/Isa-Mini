theory Test_Contradiction_false_goal
  imports Minilang_Agent.Minilang_Agent
begin

lemma "False \<Longrightarrow> False"
  by aoa

end
