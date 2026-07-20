theory Test_Contradiction_false_goal
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Contradiction_false_goal"]]

lemma "False \<Longrightarrow> False"
  by aoa

end
