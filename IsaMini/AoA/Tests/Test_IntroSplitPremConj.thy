theory Test_IntroSplitPremConj
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.IntroSplitPremConj"]]

(* The goal has four premises exercising each destruct rule of
   deep_destruct_prem:
   - plain conj:            A ∧ B ∧ C      (splits via elim_conjs alone)
   - forall-over-conj:      ∀x. P x ∧ Q x  (rewrites all_conj_distrib, then splits)
   - implies-over-conj,
     small antecedent:      D ⟶ E ∧ F      (rewrites imp_conjR, then splits)
   - implies-over-conj,
     large antecedent:      L ⟶ G ∧ H      (smart_size L ≥ 20; NOT destructed)

   The conclusion re-combines everything so the proof still goes through
   under `aoa`. *)
lemma
  fixes A B C D E F G H :: bool
    and P Q :: "'a \<Rightarrow> bool"
    and big1 big2 big3 big4 big5 big6 big7 big8 big9 big10 big11 big12 :: bool
  shows
  "\<lbrakk> A \<and> B \<and> C;
     \<forall>x. P x \<and> Q x;
     D \<longrightarrow> E \<and> F;
     (big1 \<and> big2 \<and> big3 \<and> big4 \<and> big5 \<and> big6 \<and> big7 \<and>
      big8 \<and> big9 \<and> big10 \<and> big11 \<and> big12) \<longrightarrow> G \<and> H \<rbrakk>
   \<Longrightarrow> A \<and> B \<and> C \<and> P (SOME x. True) \<and> Q (SOME x. True) \<and> (D \<longrightarrow> E) \<and> (D \<longrightarrow> F)"
  by aoa

end
