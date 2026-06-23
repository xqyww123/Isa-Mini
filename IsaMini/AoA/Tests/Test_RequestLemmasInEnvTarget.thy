theory Test_RequestLemmasInEnvTarget
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.RequestLemmasInEnvTarget"]]

(* Force a Define's auto-prove path to fail so a deferred block with
   termination-residual obligations opens — needed to exercise the
   Define-anchor cascade re-eval (case B). The fake flag only affects
   the Define-internal prover, not the stubbed worker dispatch. *)
setup \<open>Config.put_global Minilang.fun_fake_automatic_failure true\<close>

lemma test_request_lemmas_in_env_target:
  shows "(0::nat) \<le> n"
  by aoa

end
