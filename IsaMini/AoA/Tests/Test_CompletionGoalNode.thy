theory Test_CompletionGoalNode
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.CompletionGoalNode"]]

lemma t1: "(1::int) = (1::int) \<and> (2::int) = (2::int)"
  by aoa

end
