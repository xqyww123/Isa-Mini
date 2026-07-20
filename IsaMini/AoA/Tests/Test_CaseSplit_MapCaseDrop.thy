theory Test_CaseSplit_MapCaseDrop
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.CaseSplit_MapCaseDrop"]]

lemma t_bool: "P (b::bool)"
  by aoa

end
