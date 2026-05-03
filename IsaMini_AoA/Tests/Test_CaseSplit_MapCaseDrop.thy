theory Test_CaseSplit_MapCaseDrop
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.CaseSplit_MapCaseDrop"]]

lemma t_bool: "P (b::bool)"
  by aoa

end
