theory Test_PostInstRuleTermThenType
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.PostInstRuleTermThenType"]]

consts P :: "nat \<Rightarrow> bool"
consts S :: "'a \<Rightarrow> bool"
consts k :: nat

(* Residual ?x :: ?'a (a term var) AND an independent type-only ?'b (in
   `\<forall>y::'b. y=y`). The probe asks for the TERM first; answering ?x:=0::nat pins
   ?'a but leaves ?'b, so a second TYPE round fires \<rightarrow> kinds = [term, type]. *)
lemma myrule4: "S (x::'a) \<Longrightarrow> (\<forall>y::'b. y = y) \<Longrightarrow> P m"
  sorry

lemma "P k"
  by aoa

end
