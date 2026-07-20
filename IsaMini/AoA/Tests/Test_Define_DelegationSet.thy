theory Test_Define_DelegationSet
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.Define_DelegationSet"]]

lemma define_delegation_set_test: "(0::int) \<le> x * x"
  by  aoa

end
