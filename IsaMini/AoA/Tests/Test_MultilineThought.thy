theory Test_MultilineThought
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.MultilineThought"]]

lemma "(x::int) * x \<ge> 0"
  by   aoa

end
