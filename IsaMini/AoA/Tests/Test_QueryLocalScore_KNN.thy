theory Test_QueryLocalScore_KNN
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.QueryLocalScore_KNN"]]
declare [[AoA_read_proof_store=false]]

lemma "(x::int) * x \<ge> 0"
  by aoa

end
