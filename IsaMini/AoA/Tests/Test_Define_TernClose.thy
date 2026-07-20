theory Test_Define_TernClose
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.Define_TernClose"]]

(* Depth-3 RVAR plus depth-2 RZERO base (tern (Suc (Suc 0))); tern 5 = 5 closes via both bridge kinds. *)

lemma tern_close:
  "\<exists>f :: nat \<Rightarrow> nat. f 5 = 5"
  by  aoa

end
