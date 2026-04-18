theory Test_Obtain_Fixed
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Obtain_Fixed"]]

lemma \<open>(\<exists>k::nat. k = m) \<Longrightarrow> True\<close>
  by aoa

end
