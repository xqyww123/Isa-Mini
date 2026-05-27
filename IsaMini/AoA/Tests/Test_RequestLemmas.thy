theory Test_RequestLemmas
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.RequestLemmas"]]

lemma request_lemmas_test:
  fixes x :: "int"
  assumes h1: "x \<ge> 0"
  shows "(0::int) \<le> x * x"
  by aoa

end
