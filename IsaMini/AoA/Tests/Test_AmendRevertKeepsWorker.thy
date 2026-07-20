theory Test_AmendRevertKeepsWorker
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.AmendRevertKeepsWorker"]]

definition "foo \<equiv> (0::nat) = 0"

lemma revert_keeps_worker_test:
  assumes h1: "P (x::nat)"
      and h2: "Q (y::nat)"
  shows "P x \<and> Q y"
  by   aoa

end
