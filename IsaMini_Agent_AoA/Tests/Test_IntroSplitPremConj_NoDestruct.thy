theory Test_IntroSplitPremConj_NoDestruct
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.IntroSplitPremConj_NoDestruct"]]

(* Corner case: no premise is destructible (all are atomic bool vars or
   non-conjunctive forms). split_prem_conj is a no-op here; the alias
   logic should also be inert (aliases list is empty for every prem). *)
lemma
  fixes P Q R :: bool
  shows "\<lbrakk> P; Q; R \<rbrakk> \<Longrightarrow> P \<and> Q \<and> R"
  by aoa

end
