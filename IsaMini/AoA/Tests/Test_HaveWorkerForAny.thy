theory Test_HaveWorkerForAny
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.HaveWorkerForAny"]]

lemma have_worker_forany_test:
  fixes x :: "int"
  assumes hx: "x \<ge> 0"
  shows "(0::int) \<le> x * x"
  by aoa

end
