theory Test_ForeNodeFail
  imports Complex_Main Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.ForeNodeFail"]]

lemma fore_node_fail_test:
  fixes x :: "int"
  assumes h1: "y = x + 0"
      and h2: "z = y * 1"
  shows "x = z"
  by  aoa

end
