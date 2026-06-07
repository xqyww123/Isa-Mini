theory Test_Induction_ClassifyVars
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Induction_ClassifyVars"]]

text \<open>
  Fixture for the \<open>Induction_ClassifyVars\<close> model test. After \<open>Intro\<close> fixes the
  in-scope variables \<open>n\<close> and \<open>k\<close> (the goal has no premise, so the IH-fact picker
  stays silent), an induction on \<open>n\<close> that classifies only \<open>n\<close> leaves \<open>k\<close>
  unclassified. The Induction pre-flight then asks, via
  \<open>Interaction_ClassifyInductionVars\<close>, which of the unclassified variables to
  generalize; selecting \<open>k\<close> makes it generalized (universally quantified in the
  induction hypothesis) rather than fixed.
\<close>

lemma "\<forall>(n::nat) (k::nat). n + k = k + n"
  by aoa

end
