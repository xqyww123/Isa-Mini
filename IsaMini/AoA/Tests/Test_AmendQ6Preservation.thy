theory Test_AmendQ6Preservation
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.AmendQ6Preservation"]]

lemma t1: "(x::int) * x \<ge> 0"
  by aoa

end
