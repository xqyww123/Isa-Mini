theory Test_Derive_DischargeNullName
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.Derive_DischargeNullName"]]

lemma derive_discharge_null_name:
  assumes h: "P (0::nat) \<and> Q (0::nat)"
  shows "P (0::nat)"
  by  aoa

end
