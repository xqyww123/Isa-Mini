theory Test_Rewrite_DeleteSiblingNoChange
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Rewrite_DeleteSiblingNoChange"]]

lemma test:
  assumes h1: "y = x + (1::int)"
  shows "y > x \<and> y < x + 2"
  by aoa

end
