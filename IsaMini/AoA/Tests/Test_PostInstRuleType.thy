theory Test_PostInstRuleType
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.PostInstRuleType"]]

consts P :: "nat \<Rightarrow> bool"
consts k :: nat

(* `'a` occurs only in the premise, never the conclusion, so it stays schematic
   ?'a after the rule resolves with `P k`. The probe must ask for a TYPE. *)
lemma myTrule: "(\<forall>x::'a. x = x) \<Longrightarrow> P k"
  sorry

lemma "P k"
  by aoa

end
