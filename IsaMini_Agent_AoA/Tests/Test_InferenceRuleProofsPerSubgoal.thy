theory Test_InferenceRuleProofsPerSubgoal
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.InferenceRuleProofsPerSubgoal"]]

lemma t1: "(1::int) = (1::int) \<and> (2::int) = (2::int)"
  by aoa

end
