theory Test_Induction_ClassifyVars_PartialPremise
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.Induction_ClassifyVars_PartialPremise"]]

text \<open>
  Two coverage points at once. (a) Premise-only variable: \<open>j\<close> appears ONLY in
  the premise \<open>j < n\<close>, never in the conclusion \<open>n + k = k + n\<close>; since the
  callback reads the whole leading sequent (premises \<open>\<Longrightarrow>\<close> conclusion), \<open>j\<close> must
  still be offered. (b) Partial selection: of the offered \<open>j\<close>, \<open>k\<close> the stub
  generalizes only \<open>j\<close>, leaving \<open>k\<close> fixed.
\<close>

lemma "\<forall>(n::nat) (j::nat) (k::nat). j < n \<longrightarrow> n + k = k + n"
  by aoa

end
