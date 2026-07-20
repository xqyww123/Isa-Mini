theory Test_SemanticKNN_theories_include
  imports Complex_Main Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.SemanticKNN_theories_include"]]

lemma "length (xs @ ys) = length xs + length ys"
  by  aoa

end
