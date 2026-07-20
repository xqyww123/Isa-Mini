theory Test_AttachProofInheritsIntoSubgoalMaker
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.AttachProofInheritsIntoSubgoalMaker"]]

lemma test:
  fixes n :: nat
  shows "n + 0 = n"
  by aoa

end
