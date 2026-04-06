theory Test_Sqrt2
  imports Complex_Main Minilang_Agent.Minilang_Agent
begin

declare [[smt_oracle, z3_extensions, smt_nat_as_int,
  auto_sledgehammer_params = "provers = verit z3 e spass vampire zipperposition cvc5, smt_proofs = true",
  auto_interpret_for_embedding=false, agent_AoA_driver="ClaudeCode"]]
declare [[Semantic_Embedding.embedding_model = "gemini.gemini-embedding-2",
        AoA_retrieval_forking="without_ctxt", agent_AoA_driver="ClaudeCode"]]
lemma \<open>sqrt(2) \<notin> \<rat>\<close>
  by   AgentAoA

thm GCD.semiring_gcd_class.dvd_productE

end