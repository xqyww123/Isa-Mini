theory Test_AmendRevertKeepsWorker
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.AmendRevertKeepsWorker"]]

definition "foo \<equiv> (0::nat) = 0"

lemma revert_keeps_worker_test:
  assumes h1: "P (x::nat)"
      and h2: "Q (y::nat)"
  shows "P x \<and> Q y"
  by   aoa

end
