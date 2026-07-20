theory Test_AutoIntroQ7Inject
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.AutoIntroQ7Inject"]]

lemma t1: "(x::int) * x \<ge> 0"
  by aoa

end
