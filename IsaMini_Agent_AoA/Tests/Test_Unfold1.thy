theory Test_Unfold1
  imports "HOL-Analysis.Analysis" Minilang_Agent.Minilang_Agent
begin
  
(* declare [[agent_AoA_driver="test.Unfold1"]] *)

definition XXX where "XXX (a::int) b = (a + b)"

lemma XXX_alt: "XXX a b = b + a"
  unfolding XXX_def
  by auto

(* Test 1: Simple existential - prove there exists an x equal to 5 *)
lemma witness_test1: "XXX 1 2 = 3"
  by    Agen tAoA


theorem sqrt2_not_rational:
    "sqrt 2 \<notin> \<rat>"
  by    Agen tAoA

term \<open>coprime\<close>
term \<open>prime\<close>
lemma \<open>prime (2 :: nat)\<close>
  using two_is_prime_nat by linarith

end