(*
  Authors: Albert Qiaochu Jiang
*)

theory Test_aime_1998_p3 imports
  MathBench_Prover.MathBench_Prover Minilang_Agent.Minilang_Agent
begin
declare [[auto_interpret_for_embedding=false (*, agent_AoA_driver="ChatGPT.gpt-5.5-medium"*) ]]
(* declare [[agent_AoA_driver="test.Hammer_ProveInTime"]] *)
  
theorem aime_1988_p3:
  fixes x :: real
  assumes h0 : "0 < x"
    and h1 : "log 2 (log 8 x) = log 8 (log 2 x)"
    and valid: "0 < log 8 x" "0 < log 2 x"
  shows "(log 2 x)^2 = 27"
  by aoa

end