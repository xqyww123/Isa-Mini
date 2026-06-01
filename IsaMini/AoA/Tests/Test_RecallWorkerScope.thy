theory Test_RecallWorkerScope
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.RecallWorkerScope"]]

(* Distinctive goal, left unfinished by the test, to avoid the shared proof cache *)
lemma recall_scope_test: "(0::int) \<le> x * x + x * x + (1::int)"
  by Agent AoA

end
