theory Test_Define_IrrelevantArg
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.Define_IrrelevantArg"]]

(* Non-recursive extra parameter: gadd a (Suc n); only position 1 gets bridges, a stays general. *)

lemma gadd_close:
  "\<exists>f :: nat \<Rightarrow> nat \<Rightarrow> nat. f 5 3 = 8"
  by  aoa

end
