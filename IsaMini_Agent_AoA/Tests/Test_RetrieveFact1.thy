theory Test_RetrieveFact1
  imports Complex_Main Minilang_Agent.Minilang_Agent
begin

lemma retrieve_fact_test: "0 < (x::real) \<Longrightarrow> ln (x ^ n) = real n * ln x"
  by  AgentAoA

end
