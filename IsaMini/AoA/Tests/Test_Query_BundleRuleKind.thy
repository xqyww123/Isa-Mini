theory Test_Query_BundleRuleKind
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Query_BundleRuleKind"]]
declare [[AoA_use_proof_cache=false]]

(* A mutual inductive. Its COMBINED facts are qualified by the conglomerate name
   `myeven_myodd` (not `myeven`): `myeven_myodd.intros` is a 3-member introduction
   bundle and `myeven_myodd.inducts` is a 2-member induction bundle. ('my' prefix
   avoids clashing with HOL's even/odd.) *)
inductive myeven and myodd where
  "myeven 0"
| "myeven n \<Longrightarrow> myodd (Suc n)"
| "myodd n \<Longrightarrow> myeven (Suc n)"

lemma "(x::int) * x \<ge> 0"
  by aoa

end
