theory Test_Derive_NestedDischargeTHMLeak
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.Derive_NestedDischargeTHMLeak"]]

(* Regression fixture for the raw `THM 0 raised ... OF: no unifiers` leak.
   `step` is an object-level implication while nat_induct's second premise is
   meta-level (\<And>n. ?P n \<Longrightarrow> ?P (Suc n)), so a rule-level discharge
   nat_induct[OF base step] has no unifiers (see test.py). *)
lemma derive_nested_discharge_thm_leak:
  assumes base: "P (0::nat)"
      and step: "\<forall>k::nat. P k \<longrightarrow> P (Suc k)"
  shows "P (n::nat)"
  by aoa

end
