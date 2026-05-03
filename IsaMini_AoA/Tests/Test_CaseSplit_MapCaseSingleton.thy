theory Test_CaseSplit_MapCaseSingleton
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.CaseSplit_MapCaseSingleton"]]

lemma t_bool: "P (b::bool)"
  by aoa

end
