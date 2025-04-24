text \<open>Driven by AI purely and only.\<close>

theory Minilang
  imports HOL.HOL Minilang_Base Auto_Sledgehammer.Auto_Sledgehammer
begin

ML_file \<open>./library/aux.ML\<close>
ML_file \<open>./library/proof.ML\<close>


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


end
