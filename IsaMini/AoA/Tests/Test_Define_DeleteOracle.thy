theory Test_Define_DeleteOracle
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Define_DeleteOracle"]]

(* Same generic setup as Test_Define_CommentOracle, but we DELETE the
   Define (instead of commenting it) after using halve as the witness.
   Probes whether delete shares the comment path's live-vs-assembled
   divergence (does `halve` survive deletion in the live state?). *)
setup \<open>Config.put_global Minilang.fun_fake_automatic_failure true\<close>

lemma define_delete_oracle_test: "\<exists>f :: nat \<Rightarrow> nat. f 0 = f 0"
  by  aoa

end
