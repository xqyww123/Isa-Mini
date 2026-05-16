theory Test_Define_SucIMO
  imports Minilang_Agent.Minilang_Agent
    Complex_Main
    "HOL-Computational_Algebra.Computational_Algebra"
    "HOL-Number_Theory.Number_Theory"
begin

declare [[agent_AoA_driver="test.Define_SucIMO"]]

(* Same imports as imo_1974_p3. Test whether Define with Suc
   patterns fails under this theory context. *)

theorem imo_1974_p3:
  fixes n ::nat
  shows "\<not> 5 dvd (\<Sum> k \<le> n. ((2 * n + 1) choose (2 * k + 1)) * (2^(3 * k)))"
  by  aoa

end
