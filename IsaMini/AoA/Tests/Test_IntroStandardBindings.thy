theory Test_IntroStandardBindings
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.IntroStandardBindings"]]

lemma "(A::'a set) \<subseteq> B"
  by aoa

end
