theory Test_CaseSplit_AmendReconcile_Rematch
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.CaseSplit_AmendReconcile_Rematch"]]

lemma t_bool: "P (b::bool)"
  by aoa

end
