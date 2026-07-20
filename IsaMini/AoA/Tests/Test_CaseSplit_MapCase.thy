theory Test_CaseSplit_MapCase
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.CaseSplit_MapCase"]]

lemma t_bool: "P (b::bool)"
  by aoa

end
