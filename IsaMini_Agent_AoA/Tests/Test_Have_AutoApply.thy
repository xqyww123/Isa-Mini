theory Test_Have_AutoApply
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.HaveAutoApply"]]

definition myf :: "nat \<Rightarrow> nat" where "myf n = n + 7"

lemma auto_apply_test: "myf 3 = 10"
  by aoa

end
