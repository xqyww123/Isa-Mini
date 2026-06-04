theory Test_FailurePropagation
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.FailurePropagation"]]

(* Distinctive goal, left unfinished by the test, to avoid the shared proof cache *)
lemma failure_propagation_test: "(0::int) \<le> x * x + (17::int)"
  by Agent AoA

end
