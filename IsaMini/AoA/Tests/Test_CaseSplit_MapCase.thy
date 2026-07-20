theory Test_CaseSplit_MapCase
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.CaseSplit_MapCase"]]

lemma t_bool: "P (b::bool)"
  by aoa

end
