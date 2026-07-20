theory Test_RewriteNeqFlipNoOp2
  imports Complex_Main Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.RewriteNeqFlipNoOp2"]]

lemma rewrite_neq_flip_noop2_test:
  assumes ln2_ne_0: "ln (2::real) \<noteq> 0"
  shows "(0::real) \<le> (ln 2) * (ln 2)"
  by aoa

end
