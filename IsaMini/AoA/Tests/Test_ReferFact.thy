theory Test_ReferFact
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.ReferFactByProposition"]]

lemma t1: "(x::int) * x \<ge> 0"
  sorry

end