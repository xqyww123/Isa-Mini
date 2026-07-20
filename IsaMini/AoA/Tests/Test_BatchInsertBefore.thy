theory Test_BatchInsertBefore
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.BatchInsertBefore"]]

lemma t1: "(x::int) * x \<ge> 0"
  by aoa

end
