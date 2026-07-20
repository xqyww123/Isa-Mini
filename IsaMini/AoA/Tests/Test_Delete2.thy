theory Test_Delete2
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.Delete2"]]

(* Test rewriting premises with equations *)
lemma rewrite_test:
  fixes x :: "int"
  assumes h1: "y = x + 0"
      and h2: "z = y * 1"
  shows "x = z"
  by      aoa



end
