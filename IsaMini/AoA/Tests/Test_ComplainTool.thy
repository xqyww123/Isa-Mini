theory Test_ComplainTool
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.ComplainTool"]]

lemma complain_test:
  fixes x :: "int"
  assumes h1: "x \<ge> 0"
  shows "(0::int) \<le> x * x"
  by aoa

end
