theory Test_SorryDegradation
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.SorryDegradation"]]

lemma sorry_degradation_test:
  fixes x :: "int"
  assumes h1: "x \<ge> 0"
  shows "(0::int) \<le> x * x"
  by aoa

end
