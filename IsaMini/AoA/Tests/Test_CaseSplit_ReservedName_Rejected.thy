theory Test_CaseSplit_ReservedName_Rejected
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.CaseSplit_ReservedName_Rejected"]]

lemma t_bool: "P (b::bool)"
  by aoa

end
