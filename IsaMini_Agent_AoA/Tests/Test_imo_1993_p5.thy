(*
  Authors: Wenda Li
*)

theory Test_imo_1993_p5
  imports MathBench_Prover.MathBench_Prover Minilang_Agent.Minilang_Agent
begin
declare [[auto_interpret_for_embedding=false]]
theorem imo_1993_p5:
  "\<exists> f :: nat \<Rightarrow> nat. 
    (\<forall> a b. (a < b) \<longleftrightarrow> f a < f b) 
      \<and> f 1 = 2 \<and> (\<forall> n. f (f n) = f n + n)"
  by   aoa
end   