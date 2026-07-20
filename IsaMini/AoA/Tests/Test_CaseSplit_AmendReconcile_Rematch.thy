theory Test_CaseSplit_AmendReconcile_Rematch
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.CaseSplit_AmendReconcile_Rematch"]]

lemma t_bool: "P (b::bool)"
  by aoa

end
