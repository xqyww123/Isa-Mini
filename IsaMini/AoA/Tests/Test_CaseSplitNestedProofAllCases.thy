theory Test_CaseSplitNestedProofAllCases
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.CaseSplitNestedProofAllCases"]]

lemma t_bool: "P (b::bool)"
  by aoa

end
