theory Test_IntroStandardNoIntroAfter
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.IntroStandardNoIntroAfter"]]

lemma "P \<or> Q"
  by aoa

end
