theory Test_GlobalEnv_happy
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.GlobalEnv_happy"]]

lemma global_env_happy:
  fixes x y :: "int"
  assumes h1: "y = x"
  shows "x + y = x + x"
  by    aoa

end
