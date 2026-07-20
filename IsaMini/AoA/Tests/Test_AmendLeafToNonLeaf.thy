theory Test_AmendLeafToNonLeaf
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.AmendLeafToNonLeaf"]]

lemma "(a::nat) = a"
  by Agent AoA

end
