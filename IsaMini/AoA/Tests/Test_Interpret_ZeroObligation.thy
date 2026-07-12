theory Test_Interpret_ZeroObligation
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Interpret_ZeroObligation"]]

(* N = 0 obligations: `iz_triv` fixes a parameter but assumes nothing, so the
   interpretation has no witness obligation at all. The kernel must report
   `Goals []` (num_goals_of' = 0) rather than the length of `goals_of'` (which
   is 1 for a solved state, `[True]`) -- otherwise a phantom finished child
   would appear. The block must still open and still be closed by END, since
   that END is what registers the interpretation. *)

locale iz_triv = fixes c :: nat
begin
lemma iz_add0: "c + 0 = c" by simp
end

lemma "(5::nat) + 0 = 5"
  by aoa

end
