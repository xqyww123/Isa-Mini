theory Test_Sqrt2
  imports MathBench_Prover.MathBench_Prover Minilang_Agent.Minilang_Agent
begin
declare [[auto_interpret_for_embedding=false]]
lemma \<open>sqrt(2) \<notin> \<rat>\<close>
  by  AgentAoA

lemma \<open>(2 :: real) < sqrt (5 :: real)\<close>
  by (smt (verit, ccfv_SIG) real_sqrt_four real_sqrt_le_iff)

lemma \<open>(\<forall>a (b :: nat). (a < b) = (nat (\<lfloor>real (Suc a) * (((1 :: real) + sqrt (5 :: real)) / (2 :: real))\<rfloor> - (1 :: int)) < nat (\<lfloor>real (Suc b) * (((1 :: real) + sqrt (5 :: real)) / (2 :: real))\<rfloor> - (1 :: int)))) \<and> nat (\<lfloor>real (Suc (1 :: nat)) * (((1 :: real) + sqrt (5 :: real)) / (2 :: real))\<rfloor> - (1 :: int)) = (2 :: nat) \<and> (\<forall>(n :: nat). nat (\<lfloor>real (Suc (nat (\<lfloor>real (Suc n) * (((1 :: real) + sqrt (5 :: real)) / (2 :: real))\<rfloor> - (1 :: int)))) * (((1 :: real) + sqrt (5 :: real)) / (2 :: real))\<rfloor> - (1 :: int)) = nat (\<lfloor>real (Suc n) * (((1 :: real) + sqrt (5 :: real)) / (2 :: real))\<rfloor> - (1 :: int)) + n)\<close>

end