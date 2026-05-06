theory Test_Witness3
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Witness3"]]

(* Test 3: Multiple existentials - prove there exist x and y such that x + y = 10 *)
lemma witness_test3: "\<exists>(x::nat) (y::nat). x + y = 10"
  by aoa

end
