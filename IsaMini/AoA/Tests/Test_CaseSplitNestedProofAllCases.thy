theory Test_CaseSplitNestedProofAllCases
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.CaseSplitNestedProofAllCases"]]

lemma t_bool: "P (b::bool)"
  by aoa

end
