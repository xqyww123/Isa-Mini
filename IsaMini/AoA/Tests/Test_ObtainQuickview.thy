theory Test_ObtainQuickview
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.ObtainQuickview"]]

lemma "\<lbrakk> \<exists>k::nat. k = m \<rbrakk> \<Longrightarrow> m = m"
  by aoa

end
