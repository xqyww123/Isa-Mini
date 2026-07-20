theory Test_SubagentEmptyStepId
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.SubagentEmptyStepId"]]

(* Distinctive goal, left unfinished by the test, to avoid the shared proof cache *)
lemma subagent_empty_step_id_test: "(0::int) \<le> x * x + (7::int)"
  by Agent AoA

end
