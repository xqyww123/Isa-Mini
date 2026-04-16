theory Test_InductionGeneralize
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.InductionGeneralize"]]

lemma "\<forall>(N::nat) (m::nat). m \<le> N \<longrightarrow> m * m \<le> N * N"
  by aoa

end
