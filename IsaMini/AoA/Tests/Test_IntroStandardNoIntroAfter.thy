theory Test_IntroStandardNoIntroAfter
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.IntroStandardNoIntroAfter"]]

lemma "P \<or> Q"
  by aoa

end
