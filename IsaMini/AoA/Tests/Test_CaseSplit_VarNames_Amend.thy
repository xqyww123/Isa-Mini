theory Test_CaseSplit_VarNames_Amend
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.CaseSplit_VarNames_Amend"]]

lemma "P (n::nat)"
  by aoa

end
