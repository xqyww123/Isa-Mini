theory Test_ReferFact
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.ReferFactByProposition"]]

lemma t1: "(x::int) * x \<ge> 0"
  sorry

end