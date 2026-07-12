theory Test_Interpret_QualifierConflict
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Interpret_QualifierConflict"]]

(* A qualifier must be unique in scope: re-using one is a retryable operation
   failure carrying
     Qualifier "<q>" is already used in this proof. Pick a fresh one.
   The uniqueness table lives in the Proof.context (Proof_Data), and the
   qualifier is only entered into it when the interpretation's block CLOSES. *)

locale iq_pos = fixes p :: nat assumes iq_bp: "p > 0"
begin
lemma iq_dbl_pos: "p + p > 0" using iq_bp by simp
end

lemma "(0::nat) < 4 + 4"
  by aoa

end
