theory Test_CaseSplit_AmendReconcile_Drop
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.CaseSplit_AmendReconcile_Drop"]]

lemma t_bool: "P (b::bool)"
  by aoa

end
