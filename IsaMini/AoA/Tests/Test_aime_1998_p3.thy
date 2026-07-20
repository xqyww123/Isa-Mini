(*
  Authors: Albert Qiaochu Jiang
*)

theory Test_aime_1998_p3 imports Complex_Main
  MathBench_Prover.MathBench_Prover Minilang_AoA.Minilang_AoA
begin
declare [[auto_interpret_for_embedding=false (*, AoA_driver="ChatGPT.gpt-5.5-medium"*) ]]
(* declare [[AoA_driver="test.Hammer_ProveInTime"]] *)
  
theorem aime_1988_p3:
  fixes x :: real
  assumes h0 : "0 < x"
    and h1 : "log 2 (log 8 x) = log 8 (log 2 x)"
    and valid: "0 < log 8 x" "0 < log 2 x"
  shows "(log 2 x)^2 = 27"
  by ao a

end