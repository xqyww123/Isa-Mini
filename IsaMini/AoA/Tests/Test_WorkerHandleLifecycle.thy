theory Test_WorkerHandleLifecycle
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.WorkerHandleLifecycle"]]

(* Distinctive goal, left unfinished by the test, to avoid the shared proof cache *)
lemma worker_handle_lifecycle_test: "(0::int) \<le> x * x + (11::int)"
  by Agent AoA

end
