theory Test_NestedWorkerScope
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.NestedWorkerScope"]]

(* Distinctive goal, left unfinished by the test, to avoid the shared proof cache *)
lemma nested_worker_scope_test: "(0::int) \<le> x * x + (5::int)"
  by Agent AoA

end
