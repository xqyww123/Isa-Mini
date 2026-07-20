theory Test_CaseSplit_AmendReconcile_ExactMatch
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.CaseSplit_AmendReconcile_ExactMatch"]]

lemma t_bool: "P (b::bool)"
  by aoa

end
