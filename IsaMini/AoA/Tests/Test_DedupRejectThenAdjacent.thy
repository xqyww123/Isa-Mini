theory Test_DedupRejectThenAdjacent
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.DedupRejectThenAdjacent"]]

lemma t1: "(1::real) \<le> 2"
  by   aoa

end
