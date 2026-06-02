theory Test_EditConfine_Worker
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.EditConfine_Worker"]]

(* Distinctive goal, left unfinished by the test, to avoid the shared proof cache *)
lemma editconfine_worker_test: "(0::int) \<le> x * x + (3::int)"
  by Agent AoA

end
