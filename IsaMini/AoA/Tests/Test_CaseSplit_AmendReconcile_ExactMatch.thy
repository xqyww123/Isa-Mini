theory Test_CaseSplit_AmendReconcile_ExactMatch
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.CaseSplit_AmendReconcile_ExactMatch"]]

lemma t_bool: "P (b::bool)"
  by aoa

end
