theory Test_PostInstRule
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.PostInstRule"]]

consts P :: "nat \<Rightarrow> bool"
consts Q :: "nat \<Rightarrow> bool"
consts k :: nat

(* `c` and `m` are free \<rightarrow> schematic ?c, ?m once stored. Applying this as an
   inference rule to goal `P k` pins ?m:=k by unification, but leaves ?c
   residual in the non-consume premise `Q ?c` \<rightarrow> the post-rule probe must ask
   the agent to instantiate it. *)
lemma myrule: "P 0 \<Longrightarrow> Q c \<Longrightarrow> (\<And>n. P n \<Longrightarrow> P (Suc n)) \<Longrightarrow> P m"
  sorry

lemma "P k"
  by aoa

end
