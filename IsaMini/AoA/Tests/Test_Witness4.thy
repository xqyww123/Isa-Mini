theory Test_Witness4
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Witness4"]]

(* Test 4: Partial instantiation - witness x and y in separate steps *)
lemma witness_test4: "\<exists>(x::nat) (y::nat). x + y = 10"
  by aoa

end
