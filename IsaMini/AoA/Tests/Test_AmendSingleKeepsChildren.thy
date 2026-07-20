theory Test_AmendSingleKeepsChildren
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.AmendSingleKeepsChildren"]]

lemma t1: "(x::int) * x \<ge> 0"
  by aoa

end
