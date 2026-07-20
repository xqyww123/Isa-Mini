theory Test_RetrieveFact1
  imports Complex_Main Minilang_AoA.Minilang_AoA
begin
declare [[AoA_driver="test.RetrieveFact"]]
lemma retrieve_fact_test: "0 < (x::real) \<Longrightarrow> ln (x ^ n) = real n * ln x"
  by  aoa

end
