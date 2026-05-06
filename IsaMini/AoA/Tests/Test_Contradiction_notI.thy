theory Test_Contradiction_notI
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Contradiction_notI"]]

lemma contra_notI: "\<not> False"
  by aoa

end
