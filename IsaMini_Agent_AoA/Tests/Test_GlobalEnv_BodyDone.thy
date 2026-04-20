theory Test_GlobalEnv_BodyDone
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.GlobalEnv_BodyDone"]]

lemma global_env_body_done:
  fixes x :: "int"
  shows "x = x"
  by   aoa

end
