theory Test_Delete3
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Delete3"]]

(* Test rewriting premises with equations *)
lemma rewrite_test:
  fixes x :: "int"
  assumes h1: "y = x + 0"
      and h2: "z = y * 1"
  shows "x = z"
  by     aoa



end
