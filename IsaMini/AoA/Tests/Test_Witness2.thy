theory Test_Witness2
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Witness2"]]

lemma t2: "P = Q" for P :: bool
  by   aoa

end
