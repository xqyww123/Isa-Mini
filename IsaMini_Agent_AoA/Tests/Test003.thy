theory Test003
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.EquivDerive"]]

lemma t2: "\<forall>a. R a \<longrightarrow> (\<forall>b. P b a) = (\<forall>c. Q c a)"
  by AgentAoA
 


end