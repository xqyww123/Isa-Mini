theory Test_CaseSplit_MapCaseMixedDrop
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.CaseSplit_MapCaseMixedDrop"]]

lemma t_bool: "P (b::bool)"
  by aoa

end
