theory Test_Unfold_LocalDef
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Unfold_LocalDef"]]

(* Reproducer for term_head_not_const when Unfold targets a
   proof-local function defined via the Define operation.
   The function is a Free, not a Const, so potential_defs_of fails. *)

lemma "\<exists>f :: nat \<Rightarrow> nat. f 2 = 4 \<and> f 3 = 6"
  by  aoa

end
