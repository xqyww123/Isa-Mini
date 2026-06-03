theory Test_ValidateUnion_Reject
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.ValidateUnion_Reject"]]

lemma t1: "(1::int) = (1::int)"
  by aoa

end
