theory Test_RewriteNeqFlipNoOpDup
  imports Complex_Main Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.RewriteNeqFlipNoOpDup"]]

lemma rewrite_neq_flip_dup_test:
  assumes ln2_ne_0: "ln (2::real) \<noteq> 0"
  shows "(0::real) \<le> ln 2 * ln 2"
  by aoa

end
