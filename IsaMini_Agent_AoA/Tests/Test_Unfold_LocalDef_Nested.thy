theory Test_Unfold_LocalDef_Nested
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Unfold_LocalDef_Nested"]]

(* Reproduce the original zv bug: Define at top level, Intro splits
   conjunction, then Unfold inside a nested case block. *)
lemma "\<exists>f :: nat \<Rightarrow> nat. f 2 = 4 \<and> f 3 = 6"
  by aoa

end
