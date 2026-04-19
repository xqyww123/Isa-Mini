theory Test_InferenceRuleBatch_MultiSubgoal
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.InferenceRuleBatch_MultiSubgoal"]]

lemma t1: "(1::int) = (1::int) \<and> (2::int) = (2::int)"
  by aoa

end
