theory Test_Specialize_OverDischarge
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Derive_OverDischarge"]]

text \<open>Test that supplying more discharging facts than the rule has premises
  produces a clear error (not a raw exception THM 3 trace).\<close>

lemma specialize_over_discharge:
  assumes h_conj: "P (0::nat) \<and> Q (0::nat)"
      and h_rule: "Q (0::nat) \<longrightarrow> R (0::nat)"
  shows "R (0::nat)"
  by  aoa

end
