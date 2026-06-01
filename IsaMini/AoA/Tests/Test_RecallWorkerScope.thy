theory Test_RecallWorkerScope
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.RecallWorkerScope"]]

(* Test: `recall` line bounds under a worker-scoped proof.yaml render *)
lemma recall_scope_test: "(0::int) \<le> x * x"
  by Agent AoA

end
