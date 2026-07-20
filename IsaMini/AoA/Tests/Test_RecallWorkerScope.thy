theory Test_RecallWorkerScope
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.RecallWorkerScope"]]

(* Distinctive goal, left unfinished by the test, to avoid the shared proof cache *)
lemma recall_scope_test: "(0::int) \<le> x * x + x * x + (1::int)"
  by Agent AoA

end
