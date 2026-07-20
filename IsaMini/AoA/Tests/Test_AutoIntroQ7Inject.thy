theory Test_AutoIntroQ7Inject
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.AutoIntroQ7Inject"]]

lemma t1: "(x::int) * x \<ge> 0"
  by aoa

end
