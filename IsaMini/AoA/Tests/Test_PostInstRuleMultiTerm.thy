theory Test_PostInstRuleMultiTerm
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.PostInstRuleMultiTerm"]]

consts P :: "nat \<Rightarrow> bool"
consts Q :: "nat \<Rightarrow> bool"
consts R :: "nat \<Rightarrow> bool"
consts k :: nat

(* Two free term variables `c`, `d` in non-consume premises \<rightarrow> residual ?c, ?d
   both surfaced in a single term round. *)
lemma myrule2: "Q c \<Longrightarrow> R d \<Longrightarrow> P m"
  sorry

lemma "P k"
  by aoa

end
