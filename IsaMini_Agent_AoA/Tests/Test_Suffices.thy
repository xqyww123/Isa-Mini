theory Test_Suffices
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Suffices"]]

(* Test: Prove x^2 >= 0 by showing x^2 + 1 > 0 suffices *)
lemma suffices_test1: "(x::int) * x \<ge> 0"
  by   AgentAoA

ML \<open>Par_Exn.release_first\<close>

end
