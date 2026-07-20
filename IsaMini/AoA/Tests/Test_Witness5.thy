theory Test_Witness5
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.Witness5"]]

(* Test 5: Too many witnesses for a single leading existential *)
lemma witness_test5: "\<exists>(x::nat). x = 0"
  by aoa

end
