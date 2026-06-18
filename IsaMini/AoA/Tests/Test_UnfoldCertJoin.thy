(* Reproduces the field cert-join defect (see test.py: UnfoldCertJoin).
   Needs HOL-Analysis precompiled in the running heap (the 6666 eval REPL is
   MathBench_Prover, which includes HOL-Complex_Analysis); on a plain
   Minilang_Agent / Complex_Main heap the import below source-compiles slowly. *)
theory Test_UnfoldCertJoin
  imports Minilang_Agent.Minilang_Agent "HOL-Analysis.Elementary_Metric_Spaces"
begin
declare [[agent_AoA_driver="test.UnfoldCertJoin"]]

lemma certjoin_demo:
  "f \<in> {(f::real \<Rightarrow> real). \<exists>a c::real. 0 \<le> a \<and> f = (\<lambda>x. a / (1 - c*x)\<^sup>2)}"
  by  aoa

end
