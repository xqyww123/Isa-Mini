theory Test_ContextRestart
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.ContextRestart"]]

lemma restart_test: "(x::int) * x \<ge> 0"
  by aoa

end
