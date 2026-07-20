theory Test_DeriveBall
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.DeriveBall"]]

lemma derive_ball_test:
  assumes h1: "(0::nat) \<in> A"
      and h2: "\<forall>x\<in>A. P x"
  shows "P (0::nat)"
  by aoa

end
