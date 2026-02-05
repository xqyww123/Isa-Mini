theory Minilang_Agent
  imports Minilang.Minilang Isa_REPL.Isa_REPL Complex_Main Automation_Base.Automation_Base
          Isabelle_RPC.Remote_Procedure_Calling
begin

ML_file "helper.ML"
ML_file "agent.ML"
(* ML_file "agent.old.ML" *)
(* ML_file "model_AoA.ML" *)
ML_file "agent_packer.ML"
ML_file "agent_server.ML"
(* ML_file "tactic.ML.old"
ML_file "agent_server.old.ML"
ML_file "tactic.ML.old" *)
 
method_setup AgentAoA = \<open>
  Scan.succeed (K MiniLang_Agent_AoA.method)
\<close> 
(*
theorem sqrt2_not_rational:
    "sqrt 2 \<notin> \<rat>"
  by (AgentAoA)
*)
(*
lemma A and B and C
    apply (insert)
  apply (tactic \<open>Skip_Proof.cheat_tac \<^context> 1\<close>)
  ML_val \<open>Toplevel.proof_of @{Isar.state} |> Proof.goal\<close>

locale AA =
  fixes P :: bool and x :: \<open>'a::times\<close>
  assumes x: P
begin

ML \<open>Method.sorry_text\<close>
ML \<open>Skip_Proof.cheat_tac\<close>
lemma A: P using x sorry

lemma \<open>Q \<and> P\<close> if aaa: Q
proof -
  fix P
  note aaa
  ML_val \<open>Assumption.local_assms_of \<^context> (Local_Theory.target_of \<^context>)\<close>
  ML_val \<open>Variable.constraints_of \<^context>\<close>
  ML_val \<open>Variable.dest_fixes \<^context>\<close>
  ML_val \<open>Facts.dest_static false [(Proof_Context.facts_of (Local_Theory.target_of \<^context>))]
              (Proof_Context.facts_of \<^context>)\<close>

end
*)

end