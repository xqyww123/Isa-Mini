theory Test_Chaining
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Chaining"]]

(* Test: Chain two named facts via a mixed = / <= transitivity *)
lemma chaining_test:
  fixes a b c :: nat
  assumes ab: "a = b" and bc: "b \<le> c"
  shows "a \<le> c"
  by  aoa

end
