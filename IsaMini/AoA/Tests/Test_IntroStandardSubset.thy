theory Test_IntroStandardSubset
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.IntroStandardSubset"]]

lemma "(A::'a set) \<subseteq> B"
  by aoa

end
