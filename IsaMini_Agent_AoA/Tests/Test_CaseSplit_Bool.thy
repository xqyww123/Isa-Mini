theory Test_CaseSplit_Bool
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.CaseSplit_Bool"]]

lemma t_bool: "P (b::bool)"
  by   aoa

end
