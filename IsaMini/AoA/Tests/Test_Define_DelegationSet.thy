theory Test_Define_DelegationSet
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Define_DelegationSet"]]

lemma define_delegation_set_test: "(0::int) \<le> x * x"
  by  aoa

end
