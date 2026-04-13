theory Test_GlobalEnv
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.GlobalEnv"]]

lemma global_env_test:
  fixes x :: "int"
  assumes h1: "x = 0"
  shows "x * x = 0 \<or> P"
  by   aoa

end
