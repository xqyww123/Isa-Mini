theory Test_SubtreeStats
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.SubtreeStats"]]

lemma t1: "(x::int) * x \<ge> 0"
  by   aoa

end
