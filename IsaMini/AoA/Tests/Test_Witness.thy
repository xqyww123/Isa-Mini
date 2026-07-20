theory Test_Witness
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Witness1"]]

(* Test 1: Simple existential - prove there exists an x equal to 5 *)
lemma witness_test1: "\<exists>(x::nat). x = 5"
  by  aoa

end
