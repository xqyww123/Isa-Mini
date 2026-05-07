theory Test_Specialize_NullGap
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Derive_NullGap"]]

lemma specialize_null_gap:
  assumes h1: "P (0::nat)"
      and h2: "P (0::nat) \<longrightarrow> Q (0::nat)"
      and h3: "Q (0::nat) \<longrightarrow> R (0::nat)"
  shows "R (0::nat)"
  by  aoa

end
