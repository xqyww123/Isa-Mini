theory Test_NewScopeFactsOnResume
  imports Complex_Main Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.NewScopeFactsOnResume"]]

lemma new_scope_facts_on_resume_test:
  fixes x :: "int"
  assumes hx: "x \<ge> 0"
  shows "(0::int) \<le> x * x"
  by aoa

end
