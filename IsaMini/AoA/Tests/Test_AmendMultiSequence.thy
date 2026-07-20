theory Test_AmendMultiSequence
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.AmendMultiSequence"]]

lemma t: "(x::int) * x \<ge> 0"
  by aoa

end
