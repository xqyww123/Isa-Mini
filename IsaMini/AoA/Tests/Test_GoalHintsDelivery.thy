theory Test_GoalHintsDelivery
  imports Complex_Main Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.GoalHintsDelivery"]]

(* The running example of docs/GOAL_HINTS.md and a third hint for the Have of
   the scripted delivery test (section 7). The texts are test data. *)
declare [[aoa_notice_goal
  "To prove a divisibility `a dvd b`, look for a witness `b = a * k` (`dvd_def`), or chain through `dvd_trans`."
  whole_prop "_ dvd _"]]
declare [[aoa_notice_goal
  "`gcd` goals usually go through `gcd_unique_nat` / `gcd_dvd1` / `gcd_dvd2`."
  subterm "gcd _ _"]]
declare [[aoa_notice_goal
  "`card` goals: rewrite the set to a literal form first, then count."
  subterm "card _"]]

lemma goal_hints_delivery:
  fixes a b :: nat
  assumes "0 < a"
  shows "gcd a b dvd a \<and> 0 < a"
  by   aoa

end
