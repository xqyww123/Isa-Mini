theory Test_IntroConj
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.IntroConj"]]

lemma t2: "\<forall>a. R a \<longrightarrow> (\<forall>b. P b a) = (\<forall>c. Q c a)"
  by aoa

end
