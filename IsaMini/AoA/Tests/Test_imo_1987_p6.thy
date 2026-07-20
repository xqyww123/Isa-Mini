(*
  Authors: Albert Qiaochu Jiang
*)

theory Test_imo_1987_p6 imports
MathBench_Prover.MathBench_Prover Minilang_AoA.Minilang_AoA
begin
declare [[auto_interpret_for_embedding=false, AoA_driver="ChatGPT.gpt-5.5-medium"]]
theorem imo_1987_p6:
  fixes p :: nat
    and f :: "nat \<Rightarrow> nat"
  assumes h0 : "\<And>x. f x = x^2 + x + p"
    and h1 : "\<And>(k::nat). (k\<le>floor(sqrt (p/3))) \<Longrightarrow> prime (f k)"
  shows "\<And>i. (i \<le> p - 2) \<Longrightarrow> prime (f i)"
  by  aoa


end