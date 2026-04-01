theory Test_Have1
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Have1"]]

(* Test: Prove x^2 >= 0 by showing x^2 + 1 > 0 suffices *)
lemma suffices_test1: "(x::int) * x \<ge> 0"
  by    AgentAoA

term \<open>x + x \<ge> 0 \<Longrightarrow> x = x + 0\<close>

end
