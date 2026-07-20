theory Test_Have_AutoApply
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.HaveAutoApply"]]

definition myf :: "nat \<Rightarrow> nat" where "myf n = n + 7"

lemma auto_apply_test: "myf 3 = 10"
  by   aoa

end
