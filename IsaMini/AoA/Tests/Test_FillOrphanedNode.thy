theory Test_FillOrphanedNode
  imports Complex_Main Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.FillOrphanedNode"]]

lemma fill_orphaned_test:
  fixes x :: "int"
  assumes h: "x > 0"
  shows "x * x > 0"
  by  aoa

end
