theory Test_Interpret_ManyFacts
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.Interpret_ManyFacts"]]

(* More than 16 imported facts. The kernel registers them all (so they stay
   reachable by name and by semantic search) but does NOT inject them into the
   successors' premises; instead it reports the count, which the node renders as
   "N facts are available now. Use `query` to search them semantically". *)

locale imf_pos = fixes p :: nat assumes imf_bp: "p > 0"
begin
lemma imf_l01: "p + 1 > 1" using imf_bp by simp
lemma imf_l02: "p + 2 > 2" using imf_bp by simp
lemma imf_l03: "p + 3 > 3" using imf_bp by simp
lemma imf_l04: "p + 4 > 4" using imf_bp by simp
lemma imf_l05: "p + 5 > 5" using imf_bp by simp
lemma imf_l06: "p + 6 > 6" using imf_bp by simp
lemma imf_l07: "p + 7 > 7" using imf_bp by simp
lemma imf_l08: "p + 8 > 8" using imf_bp by simp
lemma imf_l09: "p + 9 > 9" using imf_bp by simp
lemma imf_l10: "p + 10 > 10" using imf_bp by simp
lemma imf_l11: "p + 11 > 11" using imf_bp by simp
lemma imf_l12: "p + 12 > 12" using imf_bp by simp
lemma imf_l13: "p + 13 > 13" using imf_bp by simp
lemma imf_l14: "p + 14 > 14" using imf_bp by simp
lemma imf_l15: "p + 15 > 15" using imf_bp by simp
lemma imf_l16: "p + 16 > 16" using imf_bp by simp
lemma imf_l17: "p + 17 > 17" using imf_bp by simp
lemma imf_l18: "p + 18 > 18" using imf_bp by simp
lemma imf_l19: "p + 19 > 19" using imf_bp by simp
lemma imf_l20: "p + 20 > 20" using imf_bp by simp
end

lemma "(1::nat) < 1 + 1"
  by aoa

end
