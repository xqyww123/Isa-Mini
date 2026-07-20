theory Test_SufficesPartialForAny
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.SufficesPartialForAny"]]

lemma "(\<forall>(n::nat) (m::nat). n + m \<ge> n) \<longrightarrow> (2::nat) + 3 \<ge> 2"
  by aoa

end
