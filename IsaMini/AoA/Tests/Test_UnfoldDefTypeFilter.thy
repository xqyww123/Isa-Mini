theory Test_UnfoldDefTypeFilter
  imports Minilang_Agent.Minilang_Agent
begin
declare [[agent_AoA_driver="test.UnfoldDefTypeFilter"]]

lemma subset_demo: "(A::'a set) \<subseteq> B \<Longrightarrow> A \<union> B = B"
  by  aoa

end
