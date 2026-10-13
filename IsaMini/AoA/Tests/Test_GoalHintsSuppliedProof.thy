theory Test_GoalHintsSuppliedProof
  imports Complex_Main Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.GoalHintsSuppliedProof"]]

(* docs/GOAL_HINTS.md section 7: a goal submitted together with its complete
   proof never had the footer that prints a hint. *)
declare [[aoa_notice_goal
  "To prove a divisibility `a dvd b`, look for a witness `b = a * k` (`dvd_def`), or chain through `dvd_trans`."
  whole_prop "_ dvd _"]]

lemma goal_hints_supplied_proof:
  fixes a b :: nat
  shows "0 < a + b + 1"
  by   aoa

end
