theory Test_DeleteStructuralRejected
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.DeleteStructuralRejected"]]

lemma t1: "(x::int) * x \<ge> 0"
  by   aoa

end
