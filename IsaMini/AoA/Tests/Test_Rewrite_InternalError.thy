theory Test_Rewrite_InternalError
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Rewrite_InternalError"]]

(* A constant whose presence triggers a faulty simproc. *)
definition "trigger_thm_err (x::nat) \<equiv> (x > 0)"

(* Simproc that deliberately throws THM on 'trigger_thm_err _' patterns.
   This simulates the kind of internal exception (THM type-conflict) that
   the Isabelle simplifier can raise on certain goals in richer sessions
   (e.g. AFP-1-PISA). *)
simproc_setup trigger_thm_err_simproc ("trigger_thm_err x") = \<open>
  K (K (fn _ => raise THM ("simulated internal error", 0, [])))
\<close>

lemma rewrite_internal_error_test:
  assumes h: "x > (0::nat)"
  shows "trigger_thm_err x"
  by aoa

end
