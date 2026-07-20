theory Test_GlobalEnv_BodyUnfilled
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.GlobalEnv_BodyUnfilled"]]

lemma global_env_body_unfilled:
  fixes x :: "int"
  shows "x = x"
  by   aoa

end
