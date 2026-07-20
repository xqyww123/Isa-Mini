theory Test_IntroPartialVars
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.IntroPartialVars"]]

lemma t_partial: "\<forall>(n::nat) a b. a + b \<le> n \<longrightarrow> a \<le> n"
  by aoa

end
