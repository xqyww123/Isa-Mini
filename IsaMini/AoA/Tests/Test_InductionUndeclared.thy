theory Test_InductionUndeclared
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.InductionUndeclared"]]

lemma induction_undeclared_test: "rev (rev l) = l"
  by  aoa

end
