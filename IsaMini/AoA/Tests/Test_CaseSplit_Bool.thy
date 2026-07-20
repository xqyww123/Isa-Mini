theory Test_CaseSplit_Bool
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.CaseSplit_Bool"]]

lemma t_bool: "P (b::bool)"
  by  aoa

end
