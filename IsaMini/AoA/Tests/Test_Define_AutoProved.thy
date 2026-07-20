theory Test_Define_AutoProved
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.Define_AutoProved"]]

(* Happy path: `double n = n + n` is non-recursive and trivially
   terminating. Isabelle's default termination / pat-completeness
   provers close everything, so the Define node's deferred block
   never opens — _deferred_block_opened stays False and no END is
   emitted for the Define frame. *)

lemma define_auto_test: "\<exists>f :: nat \<Rightarrow> nat. f 2 = 4"
  by  aoa

end
