theory Test_GlobalEnv_BodyUnfilled
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.GlobalEnv_BodyUnfilled"]]

lemma global_env_body_unfilled:
  fixes x :: "int"
  shows "x = x"
  by   aoa

end
