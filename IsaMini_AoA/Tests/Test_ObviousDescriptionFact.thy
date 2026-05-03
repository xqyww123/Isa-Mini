theory Test_ObviousDescriptionFact
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.ObviousDescriptionFact"]]

lemma test_goal: "(x::int) * x \<ge> 0"
  by aoa

end
