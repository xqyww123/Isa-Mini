theory Test_Obtain_Fixed
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Obtain_Fixed"]]

lemma \<open>(\<exists>k::nat. k = m) \<Longrightarrow> True\<close>
  by aoa

end
