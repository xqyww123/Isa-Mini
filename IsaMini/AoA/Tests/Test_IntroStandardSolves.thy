theory Test_IntroStandardSolves
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.IntroStandardSolves"]]

lemma "0 < Suc n"
  by aoa

end
