(*
  Authors: Albert Qiaochu Jiang
*)

theory Test_imo_1987_p4 imports
  MathBench_Prover.MathBench_Prover Minilang_Agent.Minilang_Agent
begin
declare [[auto_interpret_for_embedding=false]]
theorem imo_1987_p4:
  fixes f :: "nat \<Rightarrow> nat"
  shows "\<exists>(n::nat). f (f n) \<noteq> n + 1987"
  sorry

end