theory Test_SufficesStructured
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.SufficesStructured"]]

lemma "(\<forall>(n::nat). n * n \<ge> n) \<longrightarrow> (3::nat) * 3 \<ge> 3"
  by aoa

end
