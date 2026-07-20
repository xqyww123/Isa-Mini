theory Test_InferenceRuleProofsPerSubgoal
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.InferenceRuleProofsPerSubgoal"]]

lemma t1: "(1::int) = (1::int) \<and> (2::int) = (2::int)"
  by aoa

end
