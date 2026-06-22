theory Test_OutScopeVar
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.OutScopeVar"]]

text \<open>
  Fixture for the \<open>OutScopeVar\<close> model test. After \<open>Intro\<close> fixes \<open>n\<close> and
  assumes \<open>0 < n\<close>, an \<open>Induction\<close> on \<open>n\<close> that does NOT carry that premise
  leaves it referencing the now out-of-scope (skolem) variable \<open>n__\<close>.
  Referencing the stranded premise must produce an error naming \<open>n\<close> plus the
  discarding step — never the raw internal name \<open>n__\<close>.
\<close>

lemma
  fixes g :: "nat \<Rightarrow> nat"
  shows "True"
  by aoa

end
