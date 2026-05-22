theory Test_CaseSplit_NoSimp
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.CaseSplit_NoSimp"]]

lemma t_bool: "P (b::bool)"
  by  aoa

end
