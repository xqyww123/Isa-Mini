theory Test_ObtainMultiConstraint
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.ObtainMultiConstraint"]]

lemma "\<lbrakk> \<exists>k::nat. k = m \<and> k \<le> m \<rbrakk> \<Longrightarrow> m = m"
  by aoa

end
