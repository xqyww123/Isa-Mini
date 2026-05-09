theory Test_CompletionCascade
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.CompletionCascade"]]

lemma cascade_test: "(x::int) * x \<ge> 0"
  by   aoa

end
