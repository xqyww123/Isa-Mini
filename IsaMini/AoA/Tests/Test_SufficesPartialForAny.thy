theory Test_SufficesPartialForAny
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.SufficesPartialForAny"]]

lemma "(\<forall>(n::nat) (m::nat). n + m \<ge> n) \<longrightarrow> (2::nat) + 3 \<ge> 2"
  by aoa

end
