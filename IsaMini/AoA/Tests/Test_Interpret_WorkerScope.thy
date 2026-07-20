theory Test_Interpret_WorkerScope
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Interpret_WorkerScope"]]

(* Scoping of the imported facts: they are attached to the interpretation
   block's RESULT state (`_fixed_facts_after_me`), so they are visible to the
   node's SUCCESSORS only -- never inside the interpretation's own obligation
   subtree. A sub-agent dispatched onto one of the witness leaves must therefore
   not see them (it would be circular: those facts are what the leaf is paying
   for). *)

locale iw_base1 = fixes p :: nat assumes iw_bp: "p > 0"
locale iw_base2 = fixes s :: nat assumes iw_bs: "s > 0"
locale iw_derived = iw_base1 + iw_base2
begin
lemma iw_sum_pos: "p + s > 0" using iw_bp iw_bs by simp
end

lemma "(0::nat) < 2 + 3"
  by aoa

end
