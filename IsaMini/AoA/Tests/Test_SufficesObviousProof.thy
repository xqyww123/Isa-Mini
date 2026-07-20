theory Test_SufficesObviousProof
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.SufficesObviousProof"]]

lemma suffices_obvious_test: "(x::int) * x \<ge> 0"
  by   aoa

end
