theory Test_CaseSplit_InteractiveVars
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.CaseSplit_InteractiveVars"]]

lemma "P (n::nat)"
  by aoa

end
