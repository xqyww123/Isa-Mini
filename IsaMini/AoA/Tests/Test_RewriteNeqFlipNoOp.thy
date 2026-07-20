theory Test_RewriteNeqFlipNoOp
  imports Complex_Main Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.RewriteNeqFlipNoOp"]]

lemma rewrite_neq_flip_noop_test:
  assumes ln2_ne_0: "ln (2::real) \<noteq> 0"
  shows "ln (2::real) \<noteq> 0"
  by aoa

end
