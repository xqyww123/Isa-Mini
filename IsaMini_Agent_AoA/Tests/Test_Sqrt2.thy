theory Test_Sqrt2
  imports MathBench_Prover.MathBench_Prover Minilang_Agent.Minilang_Agent
begin

declare [[auto_interpret_for_embedding=false, agent_AoA_driver="ClaudeCode_Interactive"]]

lemma \<open>sqrt(2) \<notin> \<rat>\<close>
  by AgentAoA

end