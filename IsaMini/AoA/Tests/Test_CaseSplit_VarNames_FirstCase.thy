theory Test_CaseSplit_VarNames_FirstCase
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.CaseSplit_VarNames_FirstCase"]]

lemma "P (n::nat)"
  by aoa

end
