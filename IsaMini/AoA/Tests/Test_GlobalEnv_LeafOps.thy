theory Test_GlobalEnv_LeafOps
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.GlobalEnv_LeafOps"]]

lemma global_env_leaf_ops:
  fixes x :: "int"
  assumes h1: "x = 0"
  shows "x * x = 0"
  by aoa

end
