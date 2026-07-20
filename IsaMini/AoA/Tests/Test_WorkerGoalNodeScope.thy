theory Test_WorkerGoalNodeScope
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.WorkerGoalNodeScope"]]

lemma worker_scope_test:
  fixes x :: "int"
  assumes h1: "x \<ge> 0"
  shows "(0::int) \<le> x * x"
  by aoa

end
