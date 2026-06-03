theory Test_Witness6
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Witness6"]]

(* Test 6: empty witness list is rejected by the Python validator *)
lemma witness_test6: "\<exists>(x::nat). x = 0"
  by aoa

end
