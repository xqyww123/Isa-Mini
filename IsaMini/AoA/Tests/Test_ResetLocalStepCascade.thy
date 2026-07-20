theory Test_ResetLocalStepCascade
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.ResetLocalStepCascade"]]

lemma "rev (rev l) = l"
  by  aoa

end
