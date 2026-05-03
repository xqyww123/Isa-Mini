(*
  Authors: Wenda Li
*)

theory Test_imo_1990_p3 imports
  MathBench_Prover.MathBench_Prover Minilang_Agent.Minilang_Agent
begin
declare [[auto_interpret_for_embedding=false]]
theorem imo_1990_p3:
  fixes n :: nat
  assumes "2 \<le> n"
    and "n^2 dvd 2^n + 1"
  shows "n = 3"
  by  aoa

end
