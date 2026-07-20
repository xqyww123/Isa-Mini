theory Test_Define_G2Close
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.Define_G2Close"]]

(* Depth-2 multi-operand: g2 (Suc (Suc n)) (Suc (Suc k)); g2 2 2 = 2 hits the both-position bridges. *)

lemma g2_close:
  "\<exists>f :: nat \<Rightarrow> nat \<Rightarrow> nat. f 2 2 = 2"
  by  aoa

end
