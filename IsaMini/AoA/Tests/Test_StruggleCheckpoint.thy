theory Test_StruggleCheckpoint
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.StruggleCheckpoint"]]

lemma struggle_checkpoint_test:
  fixes x :: "int"
  assumes h1: "x \<ge> 0"
  shows "(0::int) \<le> x * x"
  by aoa

end
