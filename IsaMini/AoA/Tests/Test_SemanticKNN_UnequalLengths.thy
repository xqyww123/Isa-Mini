theory Test_SemanticKNN_UnequalLengths
  imports Complex_Main Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.SemanticKNN_UnequalLengths"]]

lemma "(n::nat) + 0 = n"
  by  aoa

end
