theory Test_UnfoldCondNote
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.UnfoldCondNote"]]

(* Conditional vs unconditional local definitional premises, for the one-shot
   "unfolding a conditional definition may have no effect" agent note.
   - g_cond is a CONDITIONAL def of g (premise 0 < n) -> note should fire.
   - h_eq is an UNCONDITIONAL def of h -> note should NOT fire.
   Both premise names are non-suffix (g_cond / h_eq), so discovery relies on the
   repaired Free-headed Find_Theorems channel. *)
lemma unfold_cond_note:
  assumes g_cond: "0 < n \<Longrightarrow> g n = n + (1::int)"
      and h_eq:   "h = (\<lambda>x::int. x + 1)"
  shows "g (k::int) = h k"
  by aoa

end
