theory Test_Unfold_LocalDef
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Unfold_LocalDef"]]

(* Reproducer for term_head_not_const when Unfold targets a
   proof-local function defined via the Define operation.
   The function is a Free, not a Const, so potential_defs_of fails. *)

lemma "\<exists>f :: nat \<Rightarrow> nat. f 2 = 4 \<and> f 3 = 6"
  by  aoa

end
