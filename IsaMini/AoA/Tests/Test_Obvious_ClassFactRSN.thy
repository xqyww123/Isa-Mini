theory Test_Obvious_ClassFactRSN
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Obvious_ClassFactRSN"]]

(* Regression fixture for the raw `THM 1 raised ... RSN: no unifiers` leak.
   The goal is deliberately unprovable so that sledgehammer must fail, which
   is the precondition for the leaked exception (see test.py). *)
lemma obvious_classfact_rsn: "(P::nat \<Rightarrow> bool) n"
  by aoa

end
