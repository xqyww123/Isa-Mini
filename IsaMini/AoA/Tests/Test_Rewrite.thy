theory Test_Rewrite
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Rewrite1"]]
  
(* Test rewriting premises with equations *)
lemma rewrite_test:
  assumes h1: "y = x + 0"
      and h2: "\<exists>aAa. z = y * 1 + aAa"
  shows "x = z"
  by     aoa 


end
