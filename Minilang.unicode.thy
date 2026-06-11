text ‹Driven by AI purely and only.›

theory Minilang
  imports HOL.List Auto_Sledgehammer.Auto_Sledgehammer
begin

(* declare [[ML_debugger, ML_exception_trace, ML_exception_debugger, ML_print_depth=1000]] *)

definition ‹NO_SIMP (X::'a::{}) ≡ X›

lemma NO_SIMP_cong[cong]: ‹NO_SIMP (X::'a::{}) ≡ NO_SIMP X› .

lemma Ball_All_comm:
  "(∀x∈A. ∀y. P x y) = (∀y. ∀x∈A. P x y)"
  by auto

lemma All_Ball_comm:
  "(∀x. ∀y∈B. P x y) = (∀y∈B. ∀x. P x y)"
  by auto

lemma Ball_Ball_comm:
  "(∀x∈A. ∀y∈B. P x y) = (∀y∈B. ∀x∈A. P x y)"
  by auto

lemma pull_Ball_eq:
  "(P ⟶ (∀x∈A. Q x)) ≡ (∀x∈A. P ⟶ Q x)"
  unfolding atomize_eq
  by (auto simp add: Ball_def)

(* Base layer (formerly in Minilang_Base.thy): definitions required by
   aux_thms.ML, whose MINILANG_AUX / Minilang_Aux / Thms are extended by
   aux.ML and used throughout proof.ML and the agent. *)

definition ‹TAG X ≡ X›
definition ‹GOAL (X::prop) ≡ X›
definition ‹PROTECT X ≡ X›
definition ‹ISO_ALL ≡ HOL.All›
definition ‹ISO_IMP ≡ HOL.implies›
definition ‹ISO_PROP (X::bool) ≡ X›

lemma ISO_PROP:
  ‹Trueprop (ISO_PROP P) ≡ Pure.prop (Trueprop P)›
  unfolding ISO_PROP_def Pure.prop_def .

ML_file ‹./library/aux_thms.ML›

hide_fact ISO_PROP
hide_const (open) TAG GOAL PROTECT ISO_ALL ISO_IMP ISO_PROP

ML_file ‹./library/unify_diagnostic.ML›  (* before aux.ML: xOF uses Unify_Diagnostic *)
ML_file ‹./library/aux.ML›
ML_file ‹./library/function/proof_local_lthy.ML›
ML_file ‹./library/function/proof_local_inductive.ML›
ML_file ‹./library/function/proof_local_function.ML›
ML_file ‹./library/proof.ML›


(* term Pure.eq *)

attribute_setup xOF = ‹Scan.repeat (Scan.lift (Args.$$$ "_") >> K NONE || Attrib.thm >> SOME) >> (fn Bs =>
      Thm.rule_attribute (map_filter I Bs)
        (fn ctxt => Minilang_Aux.xOF false (Context.proof_of ctxt) Bs))›

attribute_setup xof = ‹let
     val inst = Args.maybe Parse.embedded_inner_syntax;
     val concl = Args.$$$ "concl" -- Args.colon;
     val insts =
        Scan.repeat (Scan.unless concl inst) --
        Scan.optional (concl |-- Scan.repeat inst) [];
  in Scan.lift (insts -- Parse.for_fixes) >> (fn args =>
        Thm.rule_attribute [] (fn context =>
            uncurry (Minilang_Aux.xof (Context.proof_of context)) args))
 end › "positional instantiation of theorem"


attribute_setup "xwhere" = ‹let
     val ident = Parse.token
       (Parse.short_ident || Parse.long_ident || Parse.sym_ident || Parse.term_var ||
         Parse.type_ident || Parse.type_var || Parse.number)
     val var_name_parser =
       (ident >> Token.content_of) :|-- (fn x =>
         if String.isPrefix "?" x then
           case Lexicon.read_variable x of
             SOME xi => Scan.succeed (Minilang_Aux.VN_IndexName xi)
           | NONE => Scan.fail
         else Scan.succeed (Minilang_Aux.VN_Name x))
     fun peek parserX toks =
          let val (retX, toks') = parserX toks
           in ((Token.content_of (hd toks), retX), toks')
          end
     val named_insts =
          Parse.and_list1
            (Parse.position var_name_parser --
                (Args.$$$ "=" |-- peek (Parse.!!! Parse.embedded_inner_syntax) ))
            -- Parse.for_fixes
  in Scan.lift named_insts >> (fn args =>
        Thm.rule_attribute [] (fn context =>
            uncurry (Minilang_Aux.xwhere (Context.proof_of context)) args))
 end › "positional instantiation of theorem"


(* thm allI[xwhere 'a=nat] *)

(*
(*
section ‹Tests for proof-local function infrastructure›

text ‹Test Proof_Local_Inductive: define an inductive predicate proof-locally
  via @{ML Inductive.gen_add_inductive} with our proof-local add_ind_def.›

method_setup test_proof_local_ind = ‹
  Scan.succeed (fn ctxt =>
    CONTEXT_METHOD (fn _ => fn (ctxt, st) =>
      let
        val ctxt0 = ctxt |> Variable.set_body false
        val (_, ctxt') =
          Inductive.gen_add_inductive_cmd Proof_Local_Inductive.add_ind_def
            false false
            [(\<^binding>‹my_even›, SOME "nat ⇒ bool", NoSyn)]
            []
            [(((Binding.empty, []), "my_even 0"), [], []),
             (((Binding.empty, []), "my_even n ⟹ my_even (Suc (Suc n))"),
              [], [(\<^binding>‹n›, SOME "nat", NoSyn)])]
            []
            ctxt0
        val ctxt' = Variable.restore_body ctxt ctxt'
      in
        Seq.single (Seq.Result (ctxt', st))
      end))
›

lemma "True ∧ True"
  apply test_proof_local_ind
  by simp

text ‹Test Proof_Local_Function: define a recursive function proof-locally.
  The raw ML method bypasses minilang, so the caller must wrap the usage in
  a nested `proof - show ?thesis ... qed .` block for Proof_Context.export
  at `qed` to discharge the local-definition hyps.›

method_setup test_proof_local_fun = ‹
  Scan.succeed (fn ctxt =>
    CONTEXT_METHOD (fn _ => fn (ctxt, st) =>
      let
        val fixes = [(\<^binding>‹my_sum›, SOME "nat ⇒ nat", NoSyn)]
        val specs : Specification.multi_specs_cmd =
          [(((Binding.empty, []), "my_sum 0 = 0"), [], []),
           (((Binding.empty, []), "my_sum (Suc n) = Suc n + my_sum n"),
            [], [(\<^binding>‹n›, SOME "nat", NoSyn)])]
        val ctxt' = Proof_Local_Function.add_fun_cmd
              fixes specs Function_Fun.fun_config false ctxt
      in
        Seq.single (Seq.Result (ctxt', st))
      end))
›

text ‹Raw ML test — bypasses minilang and calls Proof_Local_Function.add_fun_cmd
  directly, so it does NOT benefit from minilang's FUN scope management.
  It needs the nested `proof - show ?thesis ... qed .` pattern for hyp discharge.›

lemma x: "∃(f::nat ⇒ nat). f 0 = 0"
  subgoal proof - show ?thesis
  apply  test_proof_local_fun
  apply (rule exI[where x="my_sum"])
  by simp qed .

text ‹Test FUN via minilang min_script (uses Minilang.FUN_by_fun).
  Hyp discharge is handled by minilang's conclude Proof_Context.export
  at the end of the script.›

lemma y: "∃(f::nat ⇒ nat). f 0 = 0"
  by (min_script ‹
    FUN my_fun :: "nat ⇒ nat"
      where "my_fun 0 = 0"
          | "my_fun (Suc n) = Suc n + my_fun n"
    HAVE "∃(f::nat ⇒ nat). f 0 = 0"
    CHOOSE my_fun
    END
    END
  ›)
*)


lemma "True"
    by (min_script ‹
      FUN f :: "nat ⇒ nat ⇒ nat"
        where "even n ⟹ f n m = m"
            | "odd n  ⟹ f n m = Suc m"
      END
    ›)
*)

end
