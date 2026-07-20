theory Test_CompletionCascade
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.CompletionCascade"]]

lemma cascade_test: "(x::int) * x \<ge> 0"
  by   aoa

end
