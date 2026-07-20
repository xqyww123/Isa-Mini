theory Test_NestedHaveProof
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.NestedHaveProof"]]

lemma t1: "(x::int) * x \<ge> 0"
  by aoa

end
