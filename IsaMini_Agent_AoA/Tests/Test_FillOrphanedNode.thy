theory Test_FillOrphanedNode
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.FillOrphanedNode"]]

lemma fill_orphaned_test:
  fixes x :: "int"
  assumes h: "x > 0"
  shows "x * x > 0"
  by  aoa

end
