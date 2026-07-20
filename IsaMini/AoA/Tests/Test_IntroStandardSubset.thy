theory Test_IntroStandardSubset
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.IntroStandardSubset"]]

lemma "(A::'a set) \<subseteq> B"
  by aoa

end
