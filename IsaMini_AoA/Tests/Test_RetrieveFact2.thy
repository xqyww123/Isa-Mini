theory Test_RetrieveFact2
  imports Complex_Main Minilang_Agent.Minilang_Agent
begin
declare [[agent_AoA_driver="test.RetrieveFact2"]] 
lemma retrieve_fact_test: "0 < (x::real) \<Longrightarrow> ln (x ^ n) = real n * ln x"
  by  aoa

end
