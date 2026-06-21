theory Test_Define_CommentHole
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Define_CommentHole"]]

(* Force the Define auto-prove path to fail (default prover + BY_METRIC
   sledge fallback + auto+termination_simp) so the termination residuals
   are pushed onto the minilang stack as an OPEN deferred block. The
   test leaves them open, uses `halve` as a witness, then comments the
   Define — probing whether the open obligation is silently dropped
   (the "separate Define hole"). *)
setup \<open>Config.put_global Minilang.fun_fake_automatic_failure true\<close>

lemma define_comment_hole_test: "\<exists>f :: nat \<Rightarrow> nat. f (Suc (Suc (Suc (Suc 0)))) = Suc (Suc 0)"
  by  aoa

end
