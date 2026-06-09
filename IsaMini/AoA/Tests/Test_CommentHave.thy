theory Test_CommentHave
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.CommentHave"]]

lemma t1: "(x::int) * x \<ge> 0"
  by   aoa

end
