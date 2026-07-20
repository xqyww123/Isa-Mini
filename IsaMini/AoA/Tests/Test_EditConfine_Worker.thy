theory Test_EditConfine_Worker
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.EditConfine_Worker"]]

(* Distinctive goal, left unfinished by the test, to avoid the shared proof cache *)
lemma editconfine_worker_test: "(0::int) \<le> x * x + (3::int)"
  by Agent AoA

end
