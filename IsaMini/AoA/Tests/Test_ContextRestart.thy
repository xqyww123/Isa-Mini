theory Test_ContextRestart
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.ContextRestart"]]

lemma restart_test: "(x::int) * x \<ge> 0"
  by aoa

end
