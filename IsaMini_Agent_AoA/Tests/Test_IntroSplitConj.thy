theory Test_IntroSplitConj
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.IntroSplitConj"]]

lemma
  assumes "P" "Q" "R"
  shows "P \<and> Q \<and> R"
  by  aoa

end
