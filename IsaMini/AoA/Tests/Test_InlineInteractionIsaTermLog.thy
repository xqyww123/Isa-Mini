theory Test_InlineInteractionIsaTermLog
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.InlineInteractionIsaTermLog"]]

lemma "(x::int) * x \<ge> 0"
  by aoa

end
