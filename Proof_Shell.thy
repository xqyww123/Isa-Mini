text \<open>Driven by AI purely and only.\<close>

theory Proof_Shell
  imports HOL.HOL Auto_Sledgehammer.Auto_Sledgehammer
begin

declare [[ML_debugger, ML_exception_trace]]

ML_file \<open>./library/proof.ML\<close>

ML \<open>Long_Name.explode "a.b.c" |> front\<close>

notepad begin

  fix a b c :: nat
  let ?x = \<open>a\<close>
  let ?x2.0 = \<open>b\<close>
ML_val \<open>Variable.binds_of \<^context>\<close>
  case
  ML_val \<open>Variable.constraints_of \<^context>\<close>
  have True
  apply unfold
end


end