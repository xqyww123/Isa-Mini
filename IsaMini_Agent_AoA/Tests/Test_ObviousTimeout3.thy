theory Test_ObviousTimeout3
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.ObviousTimeout_subproof"]]

lemma obvious_timeout_test3: "(x::int) * x \<ge> 0"
  by aoa

end
