theory Test_ObtainQuickview
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.ObtainQuickview"]]

lemma "\<lbrakk> \<exists>k::nat. k = m \<rbrakk> \<Longrightarrow> m = m"
  by aoa

end
