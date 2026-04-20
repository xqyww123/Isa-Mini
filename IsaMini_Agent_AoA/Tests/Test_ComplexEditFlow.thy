theory Test_ComplexEditFlow
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.ComplexEditFlow"]]

lemma t1: "(x::int) * x \<ge> 0"
  by aoa

end
