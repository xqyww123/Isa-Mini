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


end