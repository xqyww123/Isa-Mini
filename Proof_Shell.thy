text \<open>Driven by AI purely and only.\<close>

theory Proof_Shell
  imports HOL.HOL Auto_Sledgehammer.Auto_Sledgehammer
begin

declare [[ML_debugger, ML_exception_trace]]

ML_file \<open>./library/proof.ML\<close>

ML \<open>Long_Name.explode "a.b.c" |> front\<close>

notepad begin

  fix a b c :: nat
  assume X: \<open>a = b\<close>

ML_val \<open>
  let val ctxt = Variable.set_body true \<^context>
      val (_, ctxt) = Proof_Context.add_fixes [(\<^binding>\<open>a\<close>, NONE, NoSyn)] ctxt
                    |> @{print}
   in Syntax.read_term ctxt "a"
    ; @{thm X} |> Thm.prop_of |> Syntax.string_of_term ctxt |> tracing
    ; Variable.is_body ctxt
  end\<close>

  let ?x = \<open>a\<close>
  let ?x2.0 = \<open>b\<close>
ML_val \<open>Variable.binds_of \<^context>\<close>
  case
  ML_val \<open>Variable.constraints_of \<^context>\<close>
  have True
  apply unfold
end


end