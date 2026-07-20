theory Test_AmendLeafToNonLeaf
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.AmendLeafToNonLeaf"]]

lemma "(a::nat) = a"
  by Agent AoA

end
