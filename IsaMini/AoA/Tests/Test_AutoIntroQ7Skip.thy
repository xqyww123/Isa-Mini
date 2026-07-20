theory Test_AutoIntroQ7Skip
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.AutoIntroQ7Skip"]]

lemma t1: "(x::int) * x \<ge> 0"
  by aoa

end
