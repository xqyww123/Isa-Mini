theory Scratch_E2E_Schematic
  imports Minilang_AoA.Minilang_AoA
begin

(* End-to-end live-fire for the schematic-variable plan (§10):
   two top-level subgoals sharing ?x -> M9 merges them into one conjunction
   before the agent sees them; SplitConjs on the merged goal is gated (?x
   would land in both conjuncts) -> the agent must InstVarsInGoal ?x := 7,
   then split and close both sides by rule. *)

axiomatization PP :: "nat ⇒ bool" and QQ :: "nat ⇒ bool"
  where pp7: "PP 7" and qq7: "QQ 7"

schematic_goal "PP ?x" and "QQ ?x"
  by aoa

end
