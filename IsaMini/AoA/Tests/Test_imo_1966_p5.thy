(*
  Authors: Albert Qiaochu Jiang
*)

theory Test_imo_1966_p5 imports
MathBench_Prover.MathBench_Prover
Minilang_Agent.Minilang_Agent
begin
(* declare [[agent_AoA_driver="test.IMO_1966_p5"]] *) declare [[z3_extensions, auto_interpret_for_embedding=false, AoA_interactive_retrieval="no"]] term 1
theorem imo_1966_p5:
  fixes x a :: "nat \<Rightarrow> real"
  assumes "a 1 > a 2" and "a 2 > a 3" and "a 3 > a 4"
  assumes 
    h6 : "abs (a 1 - a 2) * x 2 + abs (a 1 - a 3) * x 3 + abs (a 1 - a 4) * x 4 = 1"
    and h7 : "abs (a 2 - a 1) * x 1 + abs (a 2 - a 3) * x 3 + abs (a 2 - a 4) * x 4 = 1"
    and h8 : "abs (a 3 - a 1) * x 1 + abs (a 3 - a 2) * x 2 + abs (a 3 - a 4) * x 4 = 1"
    and h9 : "abs (a 4 - a 1) * x 1 + abs (a 4 - a 2) * x 2 + abs (a 4 - a 3) * x 3 = 1"
  shows "x 2 = 0 \<and> x 3 = 0 \<and> x 1 = 1 / abs (a 1 - a 4) \<and> x 4 = 1 / abs (a 1 - a 4)"
  by a oa

end