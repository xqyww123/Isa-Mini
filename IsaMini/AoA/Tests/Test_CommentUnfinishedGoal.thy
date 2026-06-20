theory Test_CommentUnfinishedGoal
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.CommentUnfinishedGoal"]]

lemma t1: "(0::nat) = 0 \<longrightarrow> (\<exists>x::nat. (P::nat\<Rightarrow>bool) x \<and> (Q::nat\<Rightarrow>bool) x)"
  by  aoa

end
