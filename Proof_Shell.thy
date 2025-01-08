text \<open>Driven by AI purely and only.\<close>

theory Proof_Shell
  imports HOL.HOL Auto_Sledgehammer.Auto_Sledgehammer
begin

declare [[ML_debugger, ML_exception_trace]]

ML_file \<open>./library/proof.ML\<close>

notepad begin

  fix a b c :: nat
  let ?x = \<open>a\<close>

  ML_val \<open>Variable.constraints_of \<^context>\<close>

end


end