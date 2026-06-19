theory Test_PostInstRuleTermPinsType
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.PostInstRuleTermPinsType"]]

consts P :: "nat \<Rightarrow> bool"
consts S :: "'a \<Rightarrow> bool"
consts k :: nat

(* Residual ?x has schematic type ?'a. Answering ?x with a typed value
   (`0::nat`) pins ?'a:=nat via infer_instantiate, so NO separate type round
   is needed \<rightarrow> the loop converges after one (term) round. *)
lemma myrule3: "S (x::'a) \<Longrightarrow> P m"
  sorry

lemma "P k"
  by aoa

end
