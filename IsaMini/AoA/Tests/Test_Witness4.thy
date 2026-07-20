theory Test_Witness4
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Witness4"]]

(* Test 4: Partial instantiation - witness x and y in separate steps *)
lemma witness_test4: "\<exists>(x::nat) (y::nat). x + y = 10"
  by aoa

end
