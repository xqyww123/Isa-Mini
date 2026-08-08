theory Test_PostInstRuleShared
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.PostInstRuleShared"]]

consts P :: "nat \<Rightarrow> bool"
consts Q :: "nat \<Rightarrow> bool"
consts R :: "nat \<Rightarrow> bool"
consts k :: nat

(* `c` is free \<rightarrow> schematic ?c, and it occurs in TWO premises: after applying
   the rule the residual ?c spans two derived subgoals. The S4-relaxed probe
   (interact only on variables shared by \<ge>2 derived subgoals) must still fire
   here \<rightarrow> this fixture keeps the interaction covered now that the
   confined-variable fixtures no longer trigger it. *)
lemma sharedrule: "Q c \<Longrightarrow> R c \<Longrightarrow> P m"
  sorry

lemma "P k"
  by aoa

end
