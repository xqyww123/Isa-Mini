theory Test_Induction_MapCase
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Induction_MapCase"]]

lemma t_list: "rev (rev l) = l"
  by aoa

end
