theory Test_ObviousProof
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.HaveObviousProof"]]

lemma obvious_test: "(x::int) * x \<ge> 0"
  by  aoa

end
