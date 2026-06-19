theory Test_IntroStandardMultiGoal
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.IntroStandardMultiGoal"]]

lemma "(\<forall>x. P x) \<and> Q"
  by aoa

end
