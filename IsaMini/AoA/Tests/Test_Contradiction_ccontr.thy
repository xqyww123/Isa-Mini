theory Test_Contradiction_ccontr
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Contradiction_ccontr"]]

lemma contra_ccontr: "True"
  by aoa

end
