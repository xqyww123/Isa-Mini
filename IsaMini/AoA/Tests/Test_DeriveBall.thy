theory Test_DeriveBall
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.DeriveBall"]]

lemma derive_ball_test:
  assumes h1: "(0::nat) \<in> A"
      and h2: "\<forall>x\<in>A. P x"
  shows "P (0::nat)"
  by aoa

end
