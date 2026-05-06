theory Test_Obtain_Rewrite_Scope
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Obtain_Rewrite_Scope"]]

lemma \<open>(\<exists>k::nat. k = m) \<Longrightarrow> P k\<close>
  by aoa

end
