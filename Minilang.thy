text \<open>Driven by AI purely and only.\<close>

theory Minilang
  imports HOL.HOL Minilang_Base Auto_Sledgehammer.Auto_Sledgehammer
begin

ML_file \<open>./library/aux.ML\<close>
ML_file \<open>./library/proof.ML\<close>

attribute_setup OF = \<open>Attrib.thms >> (fn Bs =>
      Thm.rule_attribute Bs (fn ctxt => Minilang_Aux.xOF (Context.proof_of ctxt) Bs))\<close>

ML \<open>Thm.assume (Thm.cterm_of \<^context> \<^prop>\<open>1 + 1 = (3::nat)\<close>)\<close>
ML \<open>Thm_Deps.all_oracles [Skip_Proof.make_thm \<^theory> \<^prop>\<open>1 + 1 = (3::nat)\<close>]\<close>

end