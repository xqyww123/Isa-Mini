theory Test_PostInstValidation
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.PostInstValidation"]]

consts P :: "nat \<Rightarrow> bool"
consts Q :: "nat \<Rightarrow> bool"
consts R :: "nat \<Rightarrow> bool"
consts k :: nat

(* Two residual term vars ?c, ?d \<rightarrow> exercises the answer validator: empty,
   missing, unknown, duplicate, and type-clashing answers are all rejected
   with a clean BadAnswer, then a correct answer succeeds. *)
lemma myrule2: "Q c \<Longrightarrow> R d \<Longrightarrow> P m"
  sorry

lemma "P k"
  by aoa

end
