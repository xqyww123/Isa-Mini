theory Test_ObviousDescriptionFact
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.ObviousDescriptionFact"]]

lemma test_goal: "(x::int) * x \<ge> 0"
  by aoa

end
