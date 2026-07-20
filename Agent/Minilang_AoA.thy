theory Minilang_AoA
  imports Minilang.Minilang
          Isabelle_RPC.Remote_Procedure_Calling Semantic_Embedding.Semantic_Embedding
begin
(* declare [[ML_debugger]] *)
ML_file "helper.ML"

(* Agent Hint Registry: theory-local notice/reject hints fired when the agent
   uses a registered constant/fact. Loaded before agent.ML (which calls
   Agent_Hint.check_ and before agent_packer.ML/agent_server.ML (which pack
   Agent_Hint.HINT_NOTICE). *)
ML_file "agent_hint.ML"

attribute_setup xsymmetric = \<open>
  Scan.succeed (Thm.rule_attribute [] (fn context => fn th =>
    Minilang_Helper.xsymmetric (Context.proof_of context) th))
\<close> "recursive symmetric that enters quantifiers and connectives"

ML_file "agent.ML"
(* ML_file "agent.old.ML" *)
(* ML_file "model_AoA.ML" *)
ML_file "agent_packer.ML"
ML_file "preprocess.ML"
ML_file "agent_server.ML"
(* ML_file "tactic.ML.old"
ML_file "agent_server.old.ML"
ML_file "tactic.ML.old" *)

method_setup aoa = \<open>
  (* CONTEXT_METHOD prepends `ALLGOALS Goal.conjunction_tac`, splitting a Pure
     meta-conjunction goal `A &&& B` (as produced by multi-`shows` why3 VCs)
     into separate subgoals before the agent runs — matching how every stock
     Isabelle method handles `&&&`. A raw `K MiniLang_Agent_AoA.method` skips
     this, leaving the agent a `&&&` goal that its object-level conjunction
     ops (SplitConjs/conjI) cannot handle. *)
  Scan.succeed (K (Method.CONTEXT_METHOD MiniLang_Agent_AoA.method))
\<close>

(* AoA-agent-specific INDUCT/CASE_SPLIT tuning (consumes_policy,
 * induct_auto_insert_facts, …) is applied per-session in agent_server.ML
 * via Config.put on the session context, not as a theory-level `declare`
 * here — so non-AoA Minilang users of this theory keep the stock
 * defaults. *)


(*
ML \<open>
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
      RPC_Pretty.trim_markup (Position.here_strs pos |> fst)  (* Handles both file and ID positions *)
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
  by (aoa)
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


section \<open>Demo of inductive_cases and inductive_simps\<close>

text \<open>A toy inductive predicate: even numbers.\<close>

inductive is_even :: "nat \<Rightarrow> bool" where
  zero: "is_even 0"
| step: "is_even n \<Longrightarrow> is_even (Suc (Suc n))"


subsection \<open>The raw \<open>cases\<close> rule is general but clumsy\<close>

text \<open>Isabelle auto-generates \<open>is_even.cases\<close> from the introduction rules:
  \<^prop>\<open>\<lbrakk>is_even a; a = 0 \<Longrightarrow> P; \<And>n. \<lbrakk>a = Suc (Suc n); is_even n\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P\<close>

  Using it requires manually discharging the impossible cases when you
  know something about \<open>a\<close>.\<close>

lemma "is_even (Suc 0) \<Longrightarrow> False"
  apply (erule is_even.cases)
   apply simp        \<comment> \<open>case a=0: contradiction Suc 0 = 0\<close>
  apply simp         \<comment> \<open>case a=Suc(Suc n): contradiction Suc 0 = Suc(Suc n)\<close>
  done


subsection \<open>\<open>inductive_cases\<close>: a simplified, specialized elimination rule\<close>

text \<open>\<open>inductive_cases\<close> pre-analyses the introduction rules and builds a
  rule specialized to a particular form of the predicate argument.\<close>

inductive_cases is_even_Suc0E: "is_even (Suc 0)"

text \<open>This produces the theorem (printed via \<open>thm\<close>):
  @{thm is_even_Suc0E}

  i.e.  \<^prop>\<open>is_even (Suc 0) \<Longrightarrow> P\<close>.  The command has automatically
  proved that neither intro rule can produce \<open>is_even (Suc 0)\<close>, so the
  rule has no surviving cases — applying it immediately closes any goal.\<close>

thm is_even_Suc0E

lemma "is_even (Suc 0) \<Longrightarrow> False"
  by (erule is_even_Suc0E)     \<comment> \<open>one-liner now\<close>


text \<open>For a more interesting case, specialize at \<open>Suc (Suc n)\<close>:\<close>

inductive_cases is_even_SucSucE: "is_even (Suc (Suc n))"

text \<open>Equivalent ML-level construction using the function \<open>Inductive.mk_cases\<close>
  directly (this is what the \<open>inductive_cases\<close> command calls underneath):\<close>

ML \<open>
val is_even_SucSucE_via_ML =
  Inductive.mk_cases \<^context> \<^prop>\<open>is_even (Suc (Suc n))\<close>
\<close>


text \<open>What about the cleanup tactic \<open>Inductive.mk_cases_tac\<close> by itself?
  It is NOT a "do case analysis" tactic — it only \emph{cleans up} the
  goal state \emph{after} the raw \<open>cases\<close> rule has been applied. To use
  it in an apply-script, you must first apply \<open>is_even.cases\<close> to set up
  the case obligations, then \<open>mk_cases_tac\<close> discharges the dead branches:\<close>
*)

no_notation BNF_Cardinal_Arithmetic.cprod (infixr "*c" 80)
no_notation BNF_Cardinal_Arithmetic.csum (infixr "+c" 65)
no_notation BNF_Cardinal_Arithmetic.cexp (infixr "^c" 90)
no_notation BNF_Wellorder_Constructions.ordIso2 (infix "=o" 50)
no_notation BNF_Wellorder_Constructions.ordLess2 (infix "=o" 50)
no_notation BNF_Wellorder_Constructions.ordLeq2 (infix "<=o" 50)

end
