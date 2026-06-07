theory Test_HaveWorkerForAny
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.HaveWorkerForAny"]]

lemma have_worker_forany_test:
  fixes x :: "int"
  shows "(0::int) \<le> x * x"
  by aoa

end
