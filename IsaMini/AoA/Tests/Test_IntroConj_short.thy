theory Test_IntroConj_short
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.IntroConj_short"]]

lemma t2: "\<forall>a. R a \<longrightarrow> (\<forall>b. P b a) = (\<forall>c. Q c a)"
  by aoa

end
