theory Test_Nested_InferenceRule_Leak
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Nested_InferenceRule_Leak"]]

lemma t: "((1::int) = 1 \<and> (2::int) = 2) \<and> (3::int) = 3"
  by  aoa

end
