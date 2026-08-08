theory Test_GateSchematic
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.GateSchematic"]]

consts PP :: "nat \<Rightarrow> bool"
consts QQ :: "nat \<Rightarrow> bool"

lemma pp7: "PP 7" sorry
lemma qq7: "QQ 7" sorry

(* The goal carries ?x in both conjuncts: Branch / CaseSplit / SplitConjs must
   be gated until InstVarsInGoal pins it. *)
schematic_goal "PP ?x \<and> QQ ?x"
  by aoa

end
