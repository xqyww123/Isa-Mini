theory Test_SemanticKNN_induction_rule
  imports Complex_Main Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.SemanticKNN_induction_rule"]]

lemma "(n::nat) + 0 = n"
  by  aoa

end
