theory Test_Obtain_Rewrite_Scope
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Obtain_Rewrite_Scope"]]

lemma \<open>(\<exists>k::nat. k = m) \<Longrightarrow> P k\<close>
  by aoa

end
