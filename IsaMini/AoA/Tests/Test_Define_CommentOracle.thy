theory Test_Define_CommentOracle
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Define_CommentOracle"]]

(* Force the Define deferred path (open termination block) as in
   Test_Define_CommentHole, but here the goal is GENERIC: it holds for
   ANY witness and needs none of `halve`'s defining equations. So the
   surviving goal CAN be closed by reflexivity even after the Define is
   commented and the termination obligation is hidden — probing whether
   that yields a false "finished". *)
setup \<open>Config.put_global Minilang.fun_fake_automatic_failure true\<close>

lemma define_comment_oracle_test: "\<exists>f :: nat \<Rightarrow> nat. f 0 = f 0"
  by  aoa

end
