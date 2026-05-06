theory Test_Induction_MapCase
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Induction_MapCase"]]

lemma t_list: "rev (rev l) = l"
  by aoa

end
