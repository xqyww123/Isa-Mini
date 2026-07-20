theory Test_Rewrite_WhereBadVar
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.Rewrite_WhereBadVar"]]

fun myf :: "nat \<Rightarrow> nat" where
  "myf n = n + 1"

lemma "myf (myf n) = n + 2"
  by aoa

end
