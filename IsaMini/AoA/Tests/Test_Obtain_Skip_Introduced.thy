theory Test_Obtain_Skip_Introduced
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Obtain_Skip_Introduced"]]

lemma \<open>(\<exists>k::nat. k = m) \<Longrightarrow> True\<close>
  by aoa

end
