theory Test_GlobalEnv_DoneQuickview
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.GlobalEnv_DoneQuickview"]]

lemma global_env_done_qv:
  fixes x y :: "int"
  assumes h1: "y = x"
  shows "x + y = x + x"
  by    aoa

end
