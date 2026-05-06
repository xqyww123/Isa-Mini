theory Test_AmendFallbackFill
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.AmendFallbackFill"]]

lemma t1:
  fixes x :: "int"
  assumes h: "x \<ge> 0"
  shows "x * x \<ge> 0"
  by aoa

end
