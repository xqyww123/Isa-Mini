theory Test_InferenceRule_ProveInTime_Backfill
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.InferenceRule_ProveInTime_Backfill"]]

(* Test: an InferenceRule whose rule is a PROVE-IN-TIME fact must get the
   proof ML found for it pasted back into the node (stage 3a, D37), so the
   assembled RULE op carries it and a replay never re-searches.  The rule
   reaches that shape the only way the edit tool allows: given by description,
   answered by the retrieval interaction with a formalized statement. *)
lemma inference_rule_prove_in_time_backfill_test:
  shows "(0::nat) < 2"
  by  aoa

end
