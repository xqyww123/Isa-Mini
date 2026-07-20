theory Test_AttachProofInheritsIntoSubgoalMaker
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.AttachProofInheritsIntoSubgoalMaker"]]

lemma test:
  fixes n :: nat
  shows "n + 0 = n"
  by aoa

end
