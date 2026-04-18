text \<open>Driven by AI purely and only.\<close>

theory Minilang
  imports HOL.List Auto_Sledgehammer.Auto_Sledgehammer
begin

(* declare [[ML_debugger, ML_exception_trace, ML_exception_debugger, ML_print_depth=1000]] *)

definition \<open>NO_SIMP (X::'a::{}) \<equiv> X\<close>

lemma NO_SIMP_cong[cong]: \<open>NO_SIMP (X::'a::{}) \<equiv> NO_SIMP X\<close> .

ML_file \<open>./library/aux.ML\<close>
ML_file \<open>./library/unify_diagnostic.ML\<close>
ML_file \<open>./library/function/proof_local_lthy.ML\<close>
ML_file \<open>./library/function/proof_local_inductive.ML\<close>
ML_file \<open>./library/function/proof_local_function.ML\<close>
ML_file \<open>./library/proof.ML\<close>


(* term Pure.eq *)

attribute_setup OF = \<open>Attrib.thms >> (fn Bs =>
      Thm.rule_attribute Bs (fn ctxt => Minilang_Aux.xOF false (Context.proof_of ctxt) Bs))\<close>

attribute_setup of = \<open>let
     val inst = Args.maybe Parse.embedded_inner_syntax;
     val concl = Args.$$$ "concl" -- Args.colon;
     val insts =
        Scan.repeat (Scan.unless concl inst) --
        Scan.optional (concl |-- Scan.repeat inst) [];
  in Scan.lift (insts -- Parse.for_fixes) >> (fn args =>
        Thm.rule_attribute [] (fn context =>
            uncurry (Minilang_Aux.xof (Context.proof_of context)) args))
 end \<close> "positional instantiation of theorem"

(*
attribute_setup "where" = \<open>let
     fun peek parserX toks =
          let val (retX, toks') = parserX toks
           in ((Token.content_of (hd toks), retX), toks')
          end
     val named_insts =
          Parse.and_list1
            (Parse.position Args.var -- 
                (Args.$$$ "=" |-- peek (Parse.!!! Parse.embedded_inner_syntax) ))
            -- Parse.for_fixes
  in Scan.lift named_insts >> (fn args =>
        Thm.rule_attribute [] (fn context =>
            uncurry (Minilang_Aux.xwhere (Context.proof_of context)) args))
 end \<close> "positional instantiation of theorem"
*)
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
