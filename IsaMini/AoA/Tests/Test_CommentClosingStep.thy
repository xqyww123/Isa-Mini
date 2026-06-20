theory Test_CommentClosingStep
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.CommentClosingStep"]]

lemma t1: "\<exists>x::nat. (P::nat\<Rightarrow>bool) x \<and> (Q::nat\<Rightarrow>bool) x"
  by  aoa

end
