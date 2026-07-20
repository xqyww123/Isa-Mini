theory Test_Induction_InteractiveVars
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Induction_InteractiveVars"]]

lemma "P (n::nat)"
  by aoa

end
