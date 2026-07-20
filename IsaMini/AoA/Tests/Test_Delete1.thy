theory Test_Delete1
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Delete1"]]

(* Test rewriting premises with equations *)
lemma rewrite_test:
  fixes x :: "int"
  assumes h1: "y = x + 0"
      and h2: "z = y * 1"
  shows "x = z"
  by    aoa



end
