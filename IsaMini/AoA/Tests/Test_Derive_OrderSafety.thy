theory Test_Derive_OrderSafety
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Derive_OrderSafety"]]

(* Regression fixture for the discharge-order bug: a discharge argument with
   its own premises (B) must not shift the premise a later argument (C)
   targets.  C is stated object-level (True \<longrightarrow> Q2) so the bulk OF fails and
   the per-argument fallback runs; the rulify retry must attach C to Q2. *)
lemma derive_order_safety:
  assumes A: "\<lbrakk>Q; Q2\<rbrakk> \<Longrightarrow> Q3"
      and B: "\<lbrakk>P1; P2\<rbrakk> \<Longrightarrow> Q"
      and C: "True \<longrightarrow> Q2"
  shows "True"
  by aoa

end
