theory Test_Define_MaxClose
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Define_MaxClose"]]

(* Depth-1 multi-Suc-operand: maxf (Suc m) (Suc n); maxf 2 3 = 3 exercises cross-position bridges. *)

lemma maxf_close:
  "\<exists>f :: nat \<Rightarrow> nat \<Rightarrow> nat. f 2 3 = 3"
  by  aoa

end
