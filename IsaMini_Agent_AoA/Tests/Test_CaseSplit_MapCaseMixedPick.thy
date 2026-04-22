theory Test_CaseSplit_MapCaseMixedPick
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.CaseSplit_MapCaseMixedPick"]]

lemma t_bool: "P (b::bool)"
  by aoa

end
