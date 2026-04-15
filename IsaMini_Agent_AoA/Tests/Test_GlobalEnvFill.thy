theory Test_GlobalEnvFill
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.GlobalEnvFill"]]

lemma global_env_fill_test:
  fixes x :: "int"
  assumes h1: "x = 0"
  shows "x * x = 0"
  by  aoa

end
