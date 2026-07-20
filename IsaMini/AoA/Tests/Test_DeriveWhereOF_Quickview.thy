theory Test_DeriveWhereOF_Quickview
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.DeriveWhereOF_Quickview"]]

lemma derive_qv:
  assumes h: "P (0::nat) \<and> Q (0::nat)"
  shows "P (0::nat)"
  by  aoa

end
