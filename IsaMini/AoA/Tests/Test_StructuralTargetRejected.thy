theory Test_StructuralTargetRejected
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.StructuralTargetRejected"]]

lemma t1: "(x::int) * x \<ge> 0"
  by   aoa

end
