theory Test_UnfoldPointFree
  imports Minilang_Agent.Minilang_Agent
begin
declare [[AoA_driver="test.UnfoldPointFree"]]

lemma point_free_demo: "reflp ((\<subseteq>) :: 'a set \<Rightarrow> 'a set \<Rightarrow> bool)"
  by  aoa

end
