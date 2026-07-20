theory Test_FailurePropagation
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.FailurePropagation"]]

(* Distinctive goal, left unfinished by the test, to avoid the shared proof cache *)
lemma failure_propagation_test: "(0::int) \<le> x * x + (17::int)"
  by Agent AoA

end
