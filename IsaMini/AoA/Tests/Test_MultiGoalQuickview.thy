theory Test_MultiGoalQuickview
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.MultiGoalQuickview"]]

lemma
  assumes "P" "Q" "R"
  shows "P" and "Q" and "R"
  by  aoa

end
