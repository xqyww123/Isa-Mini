theory Test_CaseSplit_VarNames_FirstCase
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.CaseSplit_VarNames_FirstCase"]]

lemma "P (n::nat)"
  by aoa

end
