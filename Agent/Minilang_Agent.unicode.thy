theory Minilang_Agent
  imports Minilang.Minilang Complex_Main
          Isabelle_RPC.Remote_Procedure_Calling Semantic_Embedding.Semantic_Embedding
begin
(* declare [[ML_debugger]] *)
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

ML ‹
    let
      val ctxt = \<^context>
      val simps = #simps (dest_ss (simpset_of ctxt))
      val _ = simps |> take 20 |> List.app (fn (name, thm) =>
        writeln (name ^ "  |  hint=" ^ Thm.get_name_hint thm))

      val cs = Classical.rep_cs (Classical.claset_of ctxt)
      val intros = map #1 (Item_Net.content (#safeIs cs))
      val _ = intros |> take 10 |> List.app (fn thm =>
        writeln ("intro: " ^ Thm.get_name_hint thm))

      (* Also check a specific fact from the fact table *)
      val facts = Proof_Context.facts_of ctxt
      val test_name = "HOL.conjI"  (* adjust to any known theorem *)
      val full_name = Facts.intern facts "conjI"
      val _ = writeln ("intern: " ^ full_name)
      val _ = case Facts.lookup (Context.Proof ctxt) facts full_name of
          SOME {thms, ...} => List.app (fn thm =>
            writeln ("fact hint: " ^ Thm.get_name_hint thm)) thms
        | NONE => writeln "not found"
    in () end
  ›

method_setup aoa = ‹
  Scan.succeed (K MiniLang_Agent_AoA.method)
›

method_setup goal_split = ‹
  Scan.succeed (fn ctxt =>
    SIMPLE_METHOD (Goal_Preprocess.preprocess_split_tac ctxt))
›

method_setup custom_split = ‹
  Scan.succeed (fn ctxt =>
    SIMPLE_METHOD (ALLGOALS (Goal_Preprocess.custom_split_tac ctxt)))
› ‹directly apply the recursive structural split (no size threshold)›

(*
locale A = fixes x :: bool assumes x: x
begin

lemma A: ‹x ∧ x› using x by auto

thm x
ML ‹Thm.raw_derivation_name @{thm A}›

end

ML ‹Thm.raw_derivation_name @{thm A.A}›






lemma x: "2 = 1 + (1::nat)" by auto
ML ‹BNF_Util.meta_mp›
ML ‹Thm.raw_derivation_name (Thm.transfer @{theory} BNF_Util.meta_mp)›


ML ‹
fun print_const_location thy const_name =
    let
      val space = Consts.space_of (Sign.consts_of thy);
      val entry = Name_Space.the_entry space const_name;
      val pos = #pos entry;
      val thy_name = #theory_long_name entry;
    in
      "Constant " ^ quote const_name ^
      " defined in theory " ^ thy_name ^
      RPC_Pretty.trim_markup (Position.here_strs pos |> fst)  (* Handles both file and ID positions *)
    end
›


ML ‹
let val facts = Proof_Context.facts_of \<^context>
    val full_name = Facts.intern facts "exIaaa"
 in Facts.lookup (Context.Proof \<^context>) facts full_name
end›

consts XXX :: int


ML ‹print_const_location @{theory} \<^const_name>‹NO_SIMP››

term Nil
ML ‹
local
  val consts = Sign.consts_of @{theory};  (* Get consts from theory *)
  val space = Consts.space_of consts;  (* Get name space *)
  val entry = Name_Space.the_entry space \<^const_name>‹NO_SIMP›  (* Get entry *)
in val pos = #pos entry |> Position.file_of
end
›
*)

(*
theorem sqrt2_not_rational:
    "sqrt 2 ∉ ℚ"
  by (aoa)
*)
(*
lemma A and B and C
    apply (insert)
  apply (tactic ‹Skip_Proof.cheat_tac \<^context> 1›)
  ML_val ‹Toplevel.proof_of @{Isar.state} |> Proof.goal›

locale AA =
  fixes P :: bool and x :: ‹'a::times›
  assumes x: P
begin

ML ‹Method.sorry_text›
ML ‹Skip_Proof.cheat_tac›
lemma A: P using x sorry

lemma ‹Q ∧ P› if aaa: Q
proof -
  fix P
  note aaa
  ML_val ‹Assumption.local_assms_of \<^context> (Local_Theory.target_of \<^context>)›
  ML_val ‹Variable.constraints_of \<^context>›
  ML_val ‹Variable.dest_fixes \<^context>›
  ML_val ‹Facts.dest_static false [(Proof_Context.facts_of (Local_Theory.target_of \<^context>))]
              (Proof_Context.facts_of \<^context>)›

end
*)


section ‹Demo of inductive_cases and inductive_simps›

text ‹A toy inductive predicate: even numbers.›

inductive is_even :: "nat ⇒ bool" where
  zero: "is_even 0"
| step: "is_even n ⟹ is_even (Suc (Suc n))"


subsection ‹The raw ‹cases› rule is general but clumsy›

text ‹Isabelle auto-generates ‹is_even.cases› from the introduction rules:
  \<^prop>‹⟦is_even a; a = 0 ⟹ P; ⋀n. ⟦a = Suc (Suc n); is_even n⟧ ⟹ P⟧ ⟹ P›

  Using it requires manually discharging the impossible cases when you
  know something about ‹a›.›

lemma "is_even (Suc 0) ⟹ False"
  apply (erule is_even.cases)
   apply simp        ― ‹case a=0: contradiction Suc 0 = 0›
  apply simp         ― ‹case a=Suc(Suc n): contradiction Suc 0 = Suc(Suc n)›
  done


subsection ‹‹inductive_cases›: a simplified, specialized elimination rule›

text ‹‹inductive_cases› pre-analyses the introduction rules and builds a
  rule specialized to a particular form of the predicate argument.›

inductive_cases is_even_Suc0E: "is_even (Suc 0)"

text ‹This produces the theorem (printed via ‹thm›):
  @{thm is_even_Suc0E}

  i.e.  \<^prop>‹is_even (Suc 0) ⟹ P›.  The command has automatically
  proved that neither intro rule can produce ‹is_even (Suc 0)›, so the
  rule has no surviving cases — applying it immediately closes any goal.›

thm is_even_Suc0E

lemma "is_even (Suc 0) ⟹ False"
  by (erule is_even_Suc0E)     ― ‹one-liner now›


text ‹For a more interesting case, specialize at ‹Suc (Suc n)›:›

inductive_cases is_even_SucSucE: "is_even (Suc (Suc n))"

text ‹Equivalent ML-level construction using the function ‹Inductive.mk_cases›
  directly (this is what the ‹inductive_cases› command calls underneath):›

ML ‹
val is_even_SucSucE_via_ML =
  Inductive.mk_cases \<^context> \<^prop>‹is_even (Suc (Suc n))›
›


text ‹What about the cleanup tactic ‹Inductive.mk_cases_tac› by itself?
  It is NOT a "do case analysis" tactic — it only \emph{cleans up} the
  goal state \emph{after} the raw ‹cases› rule has been applied. To use
  it in an apply-script, you must first apply ‹is_even.cases› to set up
  the case obligations, then ‹mk_cases_tac› discharges the dead branches:›

end