theory Test_QueryLocalScore_PatternOnly
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.QueryLocalScore_PatternOnly"]]
declare [[AoA_use_proof_cache=false]]

lemma "(x::int) * x \<ge> 0"
  by aoa

end
