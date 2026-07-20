theory Test_UnfoldPointFree
  imports Minilang_AoA.Minilang_AoA
begin
declare [[AoA_driver="test.UnfoldPointFree"]]

lemma point_free_demo: "reflp ((\<subseteq>) :: 'a set \<Rightarrow> 'a set \<Rightarrow> bool)"
  by  aoa

end
