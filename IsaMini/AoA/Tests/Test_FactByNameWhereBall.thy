theory Test_FactByNameWhereBall
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.FactByNameWhereBall"]]

lemma factbyname_where_ball_test:
  assumes hmem: "(0::nat) \<in> A"
      and h: "\<forall>x\<in>A. P x"
  shows "P (0::nat)"
  by aoa

end
