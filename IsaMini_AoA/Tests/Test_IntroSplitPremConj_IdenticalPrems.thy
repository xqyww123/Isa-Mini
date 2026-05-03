theory Test_IntroSplitPremConj_IdenticalPrems
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.IntroSplitPremConj_IdenticalPrems"]]

(* Corner case: two premises that are SYNTACTICALLY identical (A ∧ B).
   Rematching groups by internal_term.fst via aconv — both share the same
   key. Each should still be independently indexed by prem position in the
   goal, so we get two groups premise0(1..2) and premise1(1..2). *)
lemma
  fixes A B :: bool
  shows "\<lbrakk> A \<and> B; A \<and> B \<rbrakk> \<Longrightarrow> A \<and> B"
  by aoa

end
