theory Test_PostInstValidation
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.PostInstValidation"]]

consts P :: "nat \<Rightarrow> bool"
consts Q :: "nat \<Rightarrow> bool"
consts R :: "nat \<Rightarrow> bool"
consts k :: nat

(* Two residual term vars ?c, ?d \<rightarrow> exercises the answer validator: empty,
   missing, unknown, duplicate, and type-clashing answers are all rejected
   with a clean BadAnswer, then a correct answer succeeds.
   Both variables occur in BOTH premises: under the S4-relaxed probe only
   variables shared by \<ge>2 derived subgoals are offered, so confining each
   to its own premise would silence the interaction \<rightarrow> no validation at all. *)
lemma myrule2: "Q (c + d) \<Longrightarrow> R (c + d) \<Longrightarrow> P m"
  sorry

lemma "P k"
  by aoa

end
