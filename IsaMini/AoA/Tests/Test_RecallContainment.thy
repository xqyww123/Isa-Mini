theory Test_RecallContainment
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.RecallContainment"]]

(* Distinctive goal, left unfinished by the test, to avoid the shared proof cache *)
lemma recall_containment_test: "(0::int) \<le> x * x + x * x + x * x + (3::int)"
  by Agent AoA

end
