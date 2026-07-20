theory Test_AmendInductionNested
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.AmendInductionNested"]]

lemma "(\<Sum>i\<le>(n::nat). i) = n * (n + 1) div 2"
  by aoa

end
