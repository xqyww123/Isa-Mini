theory Test_RetrieveFact
  imports Minilang_Agent.Minilang_Agent "HOL-Analysis.Derivative"
begin

declare [[AoA_driver="test.RetrieveFact"]]

lemma retrieve_fact_test: "0 < (x::real) ⟹ ln (x ^ n) = real n * ln x"
  by   aoa

end
