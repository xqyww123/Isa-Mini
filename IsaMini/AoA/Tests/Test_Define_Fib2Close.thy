theory Test_Define_Fib2Close
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.Define_Fib2Close"]]

(* Depth-2 numeral closing: fib2 (Suc (Suc n)) pattern; fib2 4 = 3 closes via depth-2 bridges. *)

lemma fib2_close:
  "\<exists>f :: nat \<Rightarrow> nat. f 4 = 3"
  by  aoa

end
