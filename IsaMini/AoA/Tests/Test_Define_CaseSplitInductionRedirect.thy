theory Test_Define_CaseSplitInductionRedirect
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Define_CaseSplitInductionRedirect"]]

lemma define_cs_ind_redirect_test: "(n::nat) = n"
  by  aoa

end
