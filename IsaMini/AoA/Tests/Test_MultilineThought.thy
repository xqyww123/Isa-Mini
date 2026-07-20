theory Test_MultilineThought
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.MultilineThought"]]

lemma "(x::int) * x \<ge> 0"
  by   aoa

end
