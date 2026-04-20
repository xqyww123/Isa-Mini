theory Test_CaseSplitNestedProofAllCases
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.CaseSplitNestedProofAllCases"]]

lemma t_bool: "P (b::bool)"
  by aoa

end
