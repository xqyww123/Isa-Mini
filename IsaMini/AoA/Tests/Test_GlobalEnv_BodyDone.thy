theory Test_GlobalEnv_BodyDone
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.GlobalEnv_BodyDone"]]

lemma global_env_body_done:
  fixes x :: "int"
  shows "x = x"
  by   aoa

end
