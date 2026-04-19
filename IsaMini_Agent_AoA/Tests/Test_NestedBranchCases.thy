theory Test_NestedBranchCases
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.NestedBranchCases"]]

lemma t1: "(x::int) * x \<ge> 0"
  by aoa

end
