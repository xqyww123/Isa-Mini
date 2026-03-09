text \<open>Driven by AI purely and only.\<close>

theory Minilang
  imports HOL.HOL Auto_Sledgehammer.Auto_Sledgehammer
begin

declare [[ML_debugger, ML_exception_trace, ML_exception_debugger, ML_print_depth=1000]]

definition \<open>NO_SIMP (X::'a::{}) \<equiv> X\<close>

lemma NO_SIMP_cong[cong]: \<open>NO_SIMP (X::'a::{}) \<equiv> NO_SIMP X\<close> .

ML_file \<open>./library/aux.ML\<close>
ML_file \<open>./library/proof.ML\<close>

notepad begin
  assume A: \<open>\<forall>x y. P x \<longrightarrow> Q y\<close>
  thm A[THEN spec, THEN spec, THEN mp]
  thm spec
  thm impI
end

attribute_setup OF = \<open>Attrib.thms >> (fn Bs =>
      Thm.rule_attribute Bs (fn ctxt => Minilang_Aux.xOF (Context.proof_of ctxt) Bs))\<close>

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

ML \<open>
let val facts = Proof_Context.facts_of \<^context>
    val full_name = Facts.intern facts "exIaaa"
 in Facts.lookup (Context.Proof \<^context>) facts full_name
end\<close>

end
