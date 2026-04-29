theory Test_Obtain_Skip_Introduced
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Obtain_Skip_Introduced"]]

lemma \<open>(\<exists>k::nat. k = m) \<Longrightarrow> True\<close>
  by aoa

end
