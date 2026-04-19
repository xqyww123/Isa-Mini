theory Test_IntroSplitPremConj_AllRenamed
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.IntroSplitPremConj_AllRenamed"]]

(* Corner case: rename ALL atoms of a single conj group. After the renames,
   NO default-form binding (premise0(k)) should remain in prem_bindings_final
   — only the three alias entries. *)
lemma
  fixes A B C :: bool
  shows "\<lbrakk> A \<and> B \<and> C \<rbrakk> \<Longrightarrow> A \<and> B \<and> C"
  by aoa

end
