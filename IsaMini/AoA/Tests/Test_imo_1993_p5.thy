(*
  Authors: Wenda Li
*)
theory Test_imo_1993_p5
  imports
    "MathBench_Prover.MathBench_Prover"
    Minilang_AoA.Minilang_AoA
begin

declare [[auto_interpret_for_embedding=false, AoA_driver="ChatGPT.gpt-5.5-high"]]
theorem imo_1993_p5:
  "\<exists> f :: nat \<Rightarrow> nat. 
    (\<forall> a b. (a < b) \<longleftrightarrow> f a < f b) 
      \<and> f 1 = 2 \<and> (\<forall> n. f (f n) = f n + n)"
  by   a oa



end