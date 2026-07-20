theory Test_IntroEmptyBindings
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.IntroEmptyBindings"]]

lemma t_empty: "\<forall>(n::nat) a b. a + b \<le> n \<longrightarrow> a \<le> n"
  by aoa

end
