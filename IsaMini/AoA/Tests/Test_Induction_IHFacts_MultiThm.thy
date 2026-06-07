theory Test_Induction_IHFacts_MultiThm
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Induction_SelectIHFacts_MultiThm"]]

text \<open>
  Multi-theorem fact coverage for the IH-fact picker (LOW 4). The conjunctive
  premise \<open>k \<le> n \<and> k \<le> n + n\<close> destructures into a single multi-theorem fact
  \<open>premise0\<close>, surfaced under the standard 1-based indexed names \<open>premise0(1)\<close>,
  \<open>premise0(2)\<close>. Both conjuncts mention the generalized variable \<open>k\<close>, so the
  picker must offer BOTH, and selecting a strict subset must carry only the
  chosen indexed theorem (resolved through the standard fact scheme).
\<close>

lemma
  fixes a b :: "nat \<Rightarrow> nat"
  shows "\<forall>(n::nat) (k::nat). (k \<le> n \<and> k \<le> n + n) \<longrightarrow> a k dvd b n"
  by aoa

end
