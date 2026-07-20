theory Test_SufficesStructured
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.SufficesStructured"]]

lemma "(\<forall>(n::nat). n * n \<ge> n) \<longrightarrow> (3::nat) * 3 \<ge> 3"
  by aoa

end
