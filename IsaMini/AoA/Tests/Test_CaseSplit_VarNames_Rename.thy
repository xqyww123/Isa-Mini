theory Test_CaseSplit_VarNames_Rename
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.CaseSplit_VarNames_Rename"]]

lemma "P (n::nat)"
  by aoa

end
