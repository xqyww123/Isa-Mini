theory Test_QueryLocalScore_KNN
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.QueryLocalScore_KNN"]]
declare [[AoA_use_proof_cache=false]]

lemma "(x::int) * x \<ge> 0"
  by aoa

end
