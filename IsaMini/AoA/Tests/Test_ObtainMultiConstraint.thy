theory Test_ObtainMultiConstraint
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.ObtainMultiConstraint"]]

lemma "\<lbrakk> \<exists>k::nat. k = m \<and> k \<le> m \<rbrakk> \<Longrightarrow> m = m"
  by aoa

end
