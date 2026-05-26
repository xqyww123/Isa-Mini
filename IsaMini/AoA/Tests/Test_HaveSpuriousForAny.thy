theory Test_HaveSpuriousForAny
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.HaveSpuriousForAny"]]

lemma "(\<forall>(x::nat) \<in> {1..10}. x + 1 > 1) \<and> True"
  by aoa

end
