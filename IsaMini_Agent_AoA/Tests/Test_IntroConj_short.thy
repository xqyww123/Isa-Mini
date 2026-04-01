theory Test_IntroConj_short
  imports Minilang_Agent.Minilang_Agent
begin

lemma t2: "\<forall>a. R a \<longrightarrow> (\<forall>b. P b a) = (\<forall>c. Q c a)"
  by AgentAoA

end
