theory Test_AmendQ6Preservation
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.AmendQ6Preservation"]]

lemma t1: "(x::int) * x \<ge> 0"
  by aoa

end
