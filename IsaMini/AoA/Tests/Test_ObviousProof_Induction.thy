theory Test_ObviousProof_Induction
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.InductionObviousProof"]]

lemma obvious_induction_test: "rev (rev l) = l"
  by   aoa

end
