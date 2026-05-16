theory Define_Suc_NumberTheory_Test
  imports Complex_Main
    "HOL-Computational_Algebra.Computational_Algebra"
    "HOL-Number_Theory.Number_Theory"
begin

text \<open>Hypothesis: fun with Suc patterns breaks under imo_1974_p3 imports.\<close>

fun myf :: "nat \<Rightarrow> nat" where
  "myf 0 = (1::nat)"
| "myf (Suc n) = (2::nat) * myf n"

lemma "myf 3 = 8" by eval

fun tp :: "nat \<Rightarrow> nat \<times> nat" where
  "tp 0 = ((1::nat), (1::nat))"
| "tp (Suc n) = (9 * fst (tp n) + 2 * snd (tp n),
                 16 * fst (tp n) + 9 * snd (tp n))"

lemma "fst (tp 1) = 11" by eval

end
