theory Test_IntroStandardMultiGoal
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.IntroStandardMultiGoal"]]

lemma "(\<forall>x. P x) \<and> Q"
  by aoa

end
