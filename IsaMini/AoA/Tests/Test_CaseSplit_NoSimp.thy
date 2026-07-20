theory Test_CaseSplit_NoSimp
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.CaseSplit_NoSimp"]]

lemma t_bool: "P (b::bool)"
  by  aoa

end
