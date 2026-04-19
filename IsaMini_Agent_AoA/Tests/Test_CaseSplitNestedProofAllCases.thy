theory Test_CaseSplitNestedProofAllCases
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.CaseSplitNestedProofAllCases"]]

lemma t1: "(x::int) * x \<ge> 0"
  by aoa

end
