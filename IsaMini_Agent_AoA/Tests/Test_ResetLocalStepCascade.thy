theory Test_ResetLocalStepCascade
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.ResetLocalStepCascade"]]

lemma "rev (rev l) = l"
  by  aoa

end
