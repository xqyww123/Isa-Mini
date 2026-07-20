theory Test_BatchFill_HaveObvious
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.BatchFill_HaveObvious"]]

lemma t1: "(x::int) * x \<ge> 0"
  by aoa

end
