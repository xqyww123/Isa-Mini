theory Test_GlobalEnv
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.GlobalEnv"]]

lemma global_env_test:
  fixes x :: "int"
  assumes h1: "x = 0"
  shows "x * x = 0 \<or> P"
  by aoa

end
