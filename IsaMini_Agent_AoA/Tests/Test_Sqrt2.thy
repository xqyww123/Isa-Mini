theory Test_Sqrt2
  imports MathBench_Prover.MathBench_Prover Minilang_Agent.Minilang_Agent
begin

declare [[smt_oracle, z3_extensions, smt_nat_as_int,
  auto_sledgehammer_params = "provers = verit z3 e spass vampire zipperposition cvc5, smt_proofs = true",
  auto_interpret_for_embedding=false, agent_AoA_driver="ClaudeCode"]]
declare [[agent_AoA_driver="ClaudeCode", AoA_interactive_retrieval="no"]]
lemma \<open>sqrt(2) \<notin> \<rat>\<close>
  by ao a

inductive even :: \<open>nat \<Rightarrow> bool\<close> where
  \<open>even 0\<close> | \<open>even n \<Longrightarrow> even (Suc (Suc n))\<close>
thm even.induct

end