theory Test_Define_CaseSplitInductionRedirect
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Define_CaseSplitInductionRedirect"]]

lemma define_cs_ind_redirect_test: "(n::nat) = n"
  by  aoa

end
