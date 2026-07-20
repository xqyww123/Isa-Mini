theory Test_AmendInductionNested
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.AmendInductionNested"]]

lemma "(\<Sum>i\<le>(n::nat). i) = n * (n + 1) div 2"
  by aoa

end
