theory Test_ComplainTool
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.ComplainTool"]]

lemma complain_test:
  fixes x :: "int"
  assumes h1: "x \<ge> 0"
  shows "(0::int) \<le> x * x"
  by aoa

end
