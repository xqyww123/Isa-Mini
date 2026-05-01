theory Test_CaseSplit_VarNames_AllCases
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.CaseSplit_VarNames_AllCases"]]

lemma "P (l :: nat list)"
  by aoa

end
