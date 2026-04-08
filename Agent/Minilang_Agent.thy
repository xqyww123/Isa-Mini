theory Minilang_Agent
  imports Minilang.Minilang Isa_REPL.Isa_REPL Complex_Main
          Isabelle_RPC.Remote_Procedure_Calling Semantic_Embedding.Semantic_Embedding
begin                             
declare [[ML_debugger]]
ML_file "helper.ML"
ML_file "agent.ML"
(* ML_file "agent.old.ML" *)
(* ML_file "model_AoA.ML" *)
ML_file "agent_packer.ML"
ML_file "preprocess.ML"
ML_file "agent_server.ML"
(* ML_file "tactic.ML.old"
ML_file "agent_server.old.ML"
ML_file "tactic.ML.old" *)

method_setup AgentAoA = \<open>
  Scan.succeed (K MiniLang_Agent_AoA.method)
\<close>

method_setup goal_split = \<open>
  Scan.succeed (fn ctxt =>
    SIMPLE_METHOD (Goal_Preprocess.preprocess_split_tac ctxt))
\<close>

method_setup custom_split = \<open>
  Scan.succeed (fn ctxt =>
    SIMPLE_METHOD (ALLGOALS (Goal_Preprocess.custom_split_tac ctxt)))
\<close> \<open>directly apply the recursive structural split (no size threshold)\<close>

(*
locale A = fixes x :: bool assumes x: x
begin

lemma A: \<open>x \<and> x\<close> using x by auto

thm x
ML \<open>Thm.raw_derivation_name @{thm A}\<close>

end

ML \<open>Thm.raw_derivation_name @{thm A.A}\<close>






lemma x: "2 = 1 + (1::nat)" by auto
ML \<open>BNF_Util.meta_mp\<close>
ML \<open>Thm.raw_derivation_name (Thm.transfer @{theory} BNF_Util.meta_mp)\<close>


ML \<open>
fun print_const_location thy const_name =
    let
      val space = Consts.space_of (Sign.consts_of thy);
      val entry = Name_Space.the_entry space const_name;
      val pos = #pos entry;
      val thy_name = #theory_long_name entry;
    in
      "Constant " ^ quote const_name ^
      " defined in theory " ^ thy_name ^
      REPL.trim_makrup (Position.here_strs pos |> fst)  (* Handles both file and ID positions *)
    end
\<close>


ML \<open>
let val facts = Proof_Context.facts_of \<^context>
    val full_name = Facts.intern facts "exIaaa"
 in Facts.lookup (Context.Proof \<^context>) facts full_name
end\<close>

consts XXX :: int


ML \<open>print_const_location @{theory} \<^const_name>\<open>NO_SIMP\<close>\<close>

term Nil
ML \<open>
local
  val consts = Sign.consts_of @{theory};  (* Get consts from theory *)
  val space = Consts.space_of consts;  (* Get name space *)
  val entry = Name_Space.the_entry space \<^const_name>\<open>NO_SIMP\<close>  (* Get entry *)
in val pos = #pos entry |> Position.file_of
end
\<close>
*)

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