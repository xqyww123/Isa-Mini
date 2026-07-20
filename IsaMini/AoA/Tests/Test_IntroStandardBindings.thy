theory Test_IntroStandardBindings
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.IntroStandardBindings"]]

lemma "(A::'a set) \<subseteq> B"
  by aoa

end
