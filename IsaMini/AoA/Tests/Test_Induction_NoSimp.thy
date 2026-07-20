theory Test_Induction_NoSimp
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Induction_NoSimp"]]

lemma t4: "rev (rev l) = l"
  by  aoa

end
