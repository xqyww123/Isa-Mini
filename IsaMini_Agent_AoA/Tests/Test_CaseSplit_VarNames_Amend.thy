theory Test_CaseSplit_VarNames_Amend
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.CaseSplit_VarNames_Amend"]]

lemma "P (n::nat)"
  by aoa

end
