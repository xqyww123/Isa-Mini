theory Test_CaseSplitUndeclared
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.CaseSplitUndeclared"]]

lemma casesplit_undeclared_test: "rev (rev l) = l"
  by  aoa

end
