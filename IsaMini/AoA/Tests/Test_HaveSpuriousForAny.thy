theory Test_HaveSpuriousForAny
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.HaveSpuriousForAny"]]

lemma "(\<forall>(x::nat) \<in> {1..10}. x + 1 > 1) \<and> True"
  by aoa

end
