theory Test_Induction
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Induction"]]

lemma t4: "rev (rev l) = l"
  by  aoa

end
