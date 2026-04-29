theory Test_SpliceHaveRefresh
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.SpliceHaveRefresh"]]

lemma "\<not> False \<and> True"
  by aoa

end
