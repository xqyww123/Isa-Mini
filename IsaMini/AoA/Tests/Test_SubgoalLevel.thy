theory Test_SubgoalLevel
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.SubgoalLevel"]]

lemma subgoal_level_test:
  fixes x :: "int"
  assumes h1: "x \<ge> 0"
  shows "(0::int) \<le> x * x"
  by aoa

end
