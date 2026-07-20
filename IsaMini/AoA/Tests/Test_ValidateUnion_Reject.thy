theory Test_ValidateUnion_Reject
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.ValidateUnion_Reject"]]

lemma t1: "(1::int) = (1::int)"
  by aoa

end
