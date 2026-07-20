theory Test_CaseSplitUndeclared
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.CaseSplitUndeclared"]]

lemma casesplit_undeclared_test: "rev (rev l) = l"
  by  aoa

end
