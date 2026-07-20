theory Test_ObviousProof
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.HaveObviousProof"]]

lemma obvious_test: "(x::int) * x \<ge> 0"
  by  aoa

end
