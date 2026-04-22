theory Test_CaseSplit_MapCaseMixedDrop
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.CaseSplit_MapCaseMixedDrop"]]

lemma t_bool: "P (b::bool)"
  by aoa

end
