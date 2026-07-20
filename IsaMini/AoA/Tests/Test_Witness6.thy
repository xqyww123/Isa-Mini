theory Test_Witness6
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Witness6"]]

(* Test 6: empty witness list is rejected by the Python validator *)
lemma witness_test6: "\<exists>(x::nat). x = 0"
  by aoa

end
