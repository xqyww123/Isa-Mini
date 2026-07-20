theory Test_SetupRewriting_SimpNoProgress
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.SetupRewriting_SimpNoProgress"]]

lemma setup_rewriting_simp_no_progress:
  fixes f :: "int \<Rightarrow> int"
  assumes h0: "\<forall>(x :: int). f x + f (x - 1) = x ^ 2"
    and h1: "f (2::int) = (5::int)"
  shows "f (5::int) = (13::int)"
  by aoa

end
