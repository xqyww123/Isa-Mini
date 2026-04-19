(*
  Authors: Albert Qiaochu Jiang
*)

theory Test_imo_1988_p6 imports
  MathBench_Prover.MathBench_Prover Minilang_Agent.Minilang_Agent
begin
declare [[auto_interpret_for_embedding=false, smt_nat_as_int=false]]
theorem imo_1988_p6:
  fixes a b :: nat
  assumes h0 : "0<a \<and> 0<b"
    and h1 : "(a*b+1) dvd (a^2 + b^2)"
  shows "\<exists>(x::nat). ((x^2) = (a^2+b^2)/(a*b+1))"
  by  aoa

thm less_induct

declare [[induct_auto_insert_facts]]

lemma \<open>m^2 + n^2 = K * (m*n + (1::nat)) \<Longrightarrow> (\<exists>x::nat. K = x^2)\<close>
  apply (min_script \<open>
    INTRO PRINT
    INDUCT "m + n" arbitrary: m n K rule: less_induct\<close>)
  apply (induct "m + n" arbitrary: K rule: less_induct)
  thm less_induct

end