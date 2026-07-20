theory Test_CaseSplit_ReservedName_Rejected
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.CaseSplit_ReservedName_Rejected"]]

lemma t_bool: "P (b::bool)"
  by aoa

end
