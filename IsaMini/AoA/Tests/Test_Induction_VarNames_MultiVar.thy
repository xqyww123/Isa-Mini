theory Test_Induction_VarNames_MultiVar
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Induction_VarNames_MultiVar"]]

lemma "P (l :: nat list)"
  by aoa

end
