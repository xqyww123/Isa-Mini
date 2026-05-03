theory Test_AmendInductionDiscardedCtxt
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.AmendInductionDiscardedCtxt"]]

lemma "P (n::nat)"
  by aoa

end
