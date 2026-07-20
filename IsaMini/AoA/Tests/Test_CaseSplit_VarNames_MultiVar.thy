theory Test_CaseSplit_VarNames_MultiVar
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.CaseSplit_VarNames_MultiVar"]]

lemma "P (l :: nat list)"
  by aoa

end
