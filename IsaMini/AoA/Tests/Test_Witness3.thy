theory Test_Witness3
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Witness3"]]

(* Test 3: Multiple existentials - prove there exist x and y such that x + y = 10 *)
lemma witness_test3: "\<exists>(x::nat) (y::nat). x + y = 10"
  by aoa

end
