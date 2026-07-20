theory Test_Induction_IHFacts
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Induction_SelectIHFacts"]]

text \<open>
  Fixture for the \<open>Induction_SelectIHFacts\<close> model test. Mirrors the lcm
  divisibility sublemma \<open>\<forall>n k. k \<le> n \<longrightarrow> a k dvd b n\<close>: after \<open>Intro\<close> fixes
  \<open>n\<close>, \<open>k\<close> and assumes \<open>k \<le> n\<close>, an induction on \<open>n\<close> generalizing \<open>k\<close> must
  carry that premise into the induction hypothesis. The Induction pre-flight
  offers the in-scope facts mentioning the generalized variables and the agent
  selects which to carry; the selection supplements \<open>facts_to_generalize\<close>.
\<close>

lemma
  fixes a b :: "nat \<Rightarrow> nat"
  shows "\<forall>(n::nat) (k::nat). k \<le> n \<longrightarrow> a k dvd b n"
  by aoa

end
