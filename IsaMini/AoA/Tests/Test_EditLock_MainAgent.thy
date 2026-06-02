theory Test_EditLock_MainAgent
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.EditLock_MainAgent"]]

(* Distinctive goal, left unfinished by the test, to avoid the shared proof cache *)
lemma editlock_main_test: "(0::int) \<le> x * x + (2::int)"
  by Agent AoA

end
