theory Test_Witness
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Witness1"]]

(* Test 1: Simple existential - prove there exists an x equal to 5 *)
lemma witness_test1: "\<exists>(x::nat). x = 5"
  by  AgentAoA

end
