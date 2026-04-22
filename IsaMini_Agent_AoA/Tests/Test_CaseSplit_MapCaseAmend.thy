theory Test_CaseSplit_MapCaseAmend
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.CaseSplit_MapCaseAmend"]]

lemma t_bool: "P (b::bool)"
  by aoa

end
