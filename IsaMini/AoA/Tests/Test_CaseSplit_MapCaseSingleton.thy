theory Test_CaseSplit_MapCaseSingleton
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.CaseSplit_MapCaseSingleton"]]

lemma t_bool: "P (b::bool)"
  by aoa

end
