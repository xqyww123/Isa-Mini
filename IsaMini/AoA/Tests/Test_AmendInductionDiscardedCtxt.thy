theory Test_AmendInductionDiscardedCtxt
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.AmendInductionDiscardedCtxt"]]

lemma "P (n::nat)"
  by aoa

end
