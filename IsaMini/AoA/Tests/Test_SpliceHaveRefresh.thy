theory Test_SpliceHaveRefresh
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.SpliceHaveRefresh"]]

lemma "\<not> False \<and> True"
  by aoa

end
