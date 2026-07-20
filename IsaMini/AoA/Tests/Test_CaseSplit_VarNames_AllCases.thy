theory Test_CaseSplit_VarNames_AllCases
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.CaseSplit_VarNames_AllCases"]]

lemma "P (l :: nat list)"
  by aoa

end
