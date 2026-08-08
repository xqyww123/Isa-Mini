text \<open>Driven by AI purely and only.\<close>

theory Minilang
  imports HOL.List Auto_Sledgehammer.Auto_Sledgehammer
begin

(* declare [[ML_debugger, ML_exception_trace, ML_exception_debugger, ML_print_depth=1000]] *)

definition \<open>NO_SIMP (X::'a::{}) \<equiv> X\<close>

lemma NO_SIMP_cong[cong]: \<open>NO_SIMP (X::'a::{}) \<equiv> NO_SIMP X\<close> .

lemma Ball_All_comm:
  "(\<forall>x\<in>A. \<forall>y. P x y) = (\<forall>y. \<forall>x\<in>A. P x y)"
  by auto

lemma All_Ball_comm:
  "(\<forall>x. \<forall>y\<in>B. P x y) = (\<forall>y\<in>B. \<forall>x. P x y)"
  by auto

lemma Ball_Ball_comm:
  "(\<forall>x\<in>A. \<forall>y\<in>B. P x y) = (\<forall>y\<in>B. \<forall>x\<in>A. P x y)"
  by auto

lemma pull_Ball_eq:
  "(P \<longrightarrow> (\<forall>x\<in>A. Q x)) \<equiv> (\<forall>x\<in>A. P \<longrightarrow> Q x)"
  unfolding atomize_eq
  by (auto simp add: Ball_def)

(* Base layer (formerly in Minilang_Base.thy): definitions required by
   aux_thms.ML, whose MINILANG_AUX / Minilang_Aux / Thms are extended by
   aux.ML and used throughout proof.ML and the agent. *)

definition \<open>TAG X \<equiv> X\<close>
definition \<open>GOAL (X::prop) \<equiv> X\<close>
definition \<open>PROTECT X \<equiv> X\<close>

subsubsection \<open>Isomorphic Atomize (ported from phi-system PLPR)\<close>

definition \<open>pure_imp_embed \<equiv> (\<longrightarrow>)\<close>
definition pure_all_embed :: \<open>('a \<Rightarrow> bool) \<Rightarrow> bool\<close> (binder \<open>\<forall>\<^sub>e\<^sub>m\<^sub>b\<^sub>e\<^sub>d \<close> 10)
    \<comment> \<open>We give it a binder syntax to prevent eta-contraction which
        deprives names of quantifier variables\<close>
  where \<open>pure_all_embed \<equiv> (All)\<close>
definition \<open>pure_conj_embed \<equiv> (\<and>)\<close>
definition \<open>pure_prop_embed x \<equiv> x\<close>
definition \<open>pure_eq_embed \<equiv> (=)\<close>
definition \<open>pure_term_embed (x::'a::{}) \<equiv> True\<close>

ML_file \<open>./library/aux_thms.ML\<close>

ML_file \<open>./library/my_object_logic.ML\<close>

lemma [iso_atomize_rules, symmetric, iso_rulify_rules]:
  \<open>(X \<equiv> Y) \<equiv> Trueprop (pure_eq_embed X Y)\<close>
  unfolding pure_eq_embed_def atomize_eq .

lemma [iso_atomize_rules, symmetric, iso_rulify_rules]:
  \<open>(P \<Longrightarrow> Q) \<equiv> Trueprop (pure_imp_embed P Q)\<close>
  unfolding atomize_imp pure_imp_embed_def .

lemma [iso_atomize_rules, symmetric, iso_rulify_rules]:
  \<open>(P &&& Q) \<equiv> Trueprop (pure_conj_embed P Q)\<close>
  unfolding atomize_conj pure_conj_embed_def .

lemma [iso_atomize_rules, symmetric, iso_rulify_rules]:
  \<open>(\<And>x. P x) \<equiv> Trueprop (pure_all_embed (\<lambda>x. P x))\<close>
  unfolding atomize_all pure_all_embed_def .

lemma [iso_atomize_rules, symmetric, iso_rulify_rules]:
  \<open>PROP Pure.prop (Trueprop P) \<equiv> Trueprop (pure_prop_embed P)\<close>
  unfolding Pure.prop_def pure_prop_embed_def .

(* phi's 6th predefined rule, `atomize_Ball`, is NOT ported: it is stated over
   phi's own meta binder `meta_Ball` (+ `Premise`), constants Minilang does not
   have.  HOL's own `atomize_ball` is deliberately NOT used in its place: its
   LHS `(\<And>x. x \<in> A \<Longrightarrow> P x)` also matches the atomize_all/atomize_imp rules,
   which would make the rule set non-confluent. *)

lemma [iso_atomize_rules, symmetric, iso_rulify_rules]:
  \<open>(TERM (x::'a::{})) \<equiv> Trueprop (pure_term_embed x)\<close>
  unfolding pure_term_embed_def term_def
  by (rule equal_intr_rule; (rule TrueI | assumption))

hide_const (open) TAG GOAL PROTECT
  pure_imp_embed pure_all_embed pure_conj_embed pure_prop_embed pure_eq_embed
  pure_term_embed

ML_file \<open>./library/unify_diagnostic.ML\<close>  (* before aux.ML: xOF uses Unify_Diagnostic *)
ML_file \<open>./library/aux.ML\<close>
ML_file \<open>./library/function/proof_local_lthy.ML\<close>
ML_file \<open>./library/function/proof_local_inductive.ML\<close>
ML_file \<open>./library/function/proof_local_function.ML\<close>
ML_file \<open>./library/proof.ML\<close>


(* term Pure.eq *)

attribute_setup xOF = \<open>Scan.repeat (Scan.lift (Args.$$$ "_") >> K NONE || Attrib.thm >> SOME) >> (fn Bs =>
      Thm.rule_attribute (map_filter I Bs)
        (fn ctxt => Minilang_Aux.xOF false (Context.proof_of ctxt) Bs))\<close>

attribute_setup xof = \<open>let
     val inst = Args.maybe Parse.embedded_inner_syntax;
     val concl = Args.$$$ "concl" -- Args.colon;
     val insts =
        Scan.repeat (Scan.unless concl inst) --
        Scan.optional (concl |-- Scan.repeat inst) [];
  in Scan.lift (insts -- Parse.for_fixes) >> (fn args =>
        Thm.rule_attribute [] (fn context =>
            uncurry (Minilang_Aux.xof (Context.proof_of context)) args))
 end \<close> "positional instantiation of theorem"


attribute_setup "xwhere" = \<open>let
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
 end \<close> "positional instantiation of theorem"


(* thm allI[xwhere 'a=nat] *)

(*
(*
section \<open>Tests for proof-local function infrastructure\<close>

text \<open>Test Proof_Local_Inductive: define an inductive predicate proof-locally
  via @{ML Inductive.gen_add_inductive} with our proof-local add_ind_def.\<close>

method_setup test_proof_local_ind = \<open>
  Scan.succeed (fn ctxt =>
    CONTEXT_METHOD (fn _ => fn (ctxt, st) =>
      let
        val ctxt0 = ctxt |> Variable.set_body false
        val (_, ctxt') =
          Inductive.gen_add_inductive_cmd Proof_Local_Inductive.add_ind_def
            false false
            [(\<^binding>\<open>my_even\<close>, SOME "nat \<Rightarrow> bool", NoSyn)]
            []
            [(((Binding.empty, []), "my_even 0"), [], []),
             (((Binding.empty, []), "my_even n \<Longrightarrow> my_even (Suc (Suc n))"),
              [], [(\<^binding>\<open>n\<close>, SOME "nat", NoSyn)])]
            []
            ctxt0
        val ctxt' = Variable.restore_body ctxt ctxt'
      in
        Seq.single (Seq.Result (ctxt', st))
      end))
\<close>

lemma "True \<and> True"
  apply test_proof_local_ind
  by simp

text \<open>Test Proof_Local_Function: define a recursive function proof-locally.
  The raw ML method bypasses minilang, so the caller must wrap the usage in
  a nested `proof - show ?thesis ... qed .` block for Proof_Context.export
  at `qed` to discharge the local-definition hyps.\<close>

method_setup test_proof_local_fun = \<open>
  Scan.succeed (fn ctxt =>
    CONTEXT_METHOD (fn _ => fn (ctxt, st) =>
      let
        val fixes = [(\<^binding>\<open>my_sum\<close>, SOME "nat \<Rightarrow> nat", NoSyn)]
        val specs : Specification.multi_specs_cmd =
          [(((Binding.empty, []), "my_sum 0 = 0"), [], []),
           (((Binding.empty, []), "my_sum (Suc n) = Suc n + my_sum n"),
            [], [(\<^binding>\<open>n\<close>, SOME "nat", NoSyn)])]
        val ctxt' = Proof_Local_Function.add_fun_cmd
              fixes specs Function_Fun.fun_config false ctxt
      in
        Seq.single (Seq.Result (ctxt', st))
      end))
\<close>

text \<open>Raw ML test — bypasses minilang and calls Proof_Local_Function.add_fun_cmd
  directly, so it does NOT benefit from minilang's FUN scope management.
  It needs the nested `proof - show ?thesis ... qed .` pattern for hyp discharge.\<close>

lemma x: "\<exists>(f::nat \<Rightarrow> nat). f 0 = 0"
  subgoal proof - show ?thesis
  apply  test_proof_local_fun
  apply (rule exI[where x="my_sum"])
  by simp qed .

text \<open>Test FUN via minilang min_script (uses Minilang.FUN_by_fun).
  Hyp discharge is handled by minilang's conclude Proof_Context.export
  at the end of the script.\<close>

lemma y: "\<exists>(f::nat \<Rightarrow> nat). f 0 = 0"
  by (min_script \<open>
    FUN my_fun :: "nat \<Rightarrow> nat"
      where "my_fun 0 = 0"
          | "my_fun (Suc n) = Suc n + my_fun n"
    HAVE "\<exists>(f::nat \<Rightarrow> nat). f 0 = 0"
    CHOOSE my_fun
    END
    END
  \<close>)
*)


lemma "True"
    by (min_script \<open>
      FUN f :: "nat \<Rightarrow> nat \<Rightarrow> nat"
        where "even n \<Longrightarrow> f n m = m"
            | "odd n  \<Longrightarrow> f n m = Suc m"
      END
    \<close>)
*)

end
