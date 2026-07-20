theory Test_UnfoldDefTypeFilter
  imports Minilang_AoA.Minilang_AoA
begin
declare [[AoA_driver="test.UnfoldDefTypeFilter"]]

lemma subset_demo: "(A::'a set) \<subseteq> B \<Longrightarrow> A \<union> B = B"
  by  aoa

end
