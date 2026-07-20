theory Test_Interpret_MultiLeaf
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.Interpret_MultiLeaf"]]

(* N >= 2 leaves: `il_derived` inherits from two one-assumption locales, so its
   locale predicate unfolds (via the kernel's eager `unfold_locales`) into TWO
   independent leaf obligations. *)

locale il_base1 = fixes p :: nat assumes il_bp: "p > 0"
locale il_base2 = fixes s :: nat assumes il_bs: "s > 0"
locale il_derived = il_base1 + il_base2
begin
lemma il_sum_pos: "p + s > 0" using il_bp il_bs by simp
end

lemma "(0::nat) < 1 + 2"
  by aoa

end
