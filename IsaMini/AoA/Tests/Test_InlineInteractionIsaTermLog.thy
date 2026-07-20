theory Test_InlineInteractionIsaTermLog
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.InlineInteractionIsaTermLog"]]

lemma "(x::int) * x \<ge> 0"
  by aoa

end
