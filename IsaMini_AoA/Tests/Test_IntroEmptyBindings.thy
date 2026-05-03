theory Test_IntroEmptyBindings
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.IntroEmptyBindings"]]

lemma t_empty: "\<forall>(n::nat) a b. a + b \<le> n \<longrightarrow> a \<le> n"
  by aoa

end
