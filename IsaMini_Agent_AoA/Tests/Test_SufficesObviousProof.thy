theory Test_SufficesObviousProof
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.SufficesObviousProof"]]

lemma suffices_obvious_test: "(x::int) * x \<ge> 0"
  by   AgentAoA

end
