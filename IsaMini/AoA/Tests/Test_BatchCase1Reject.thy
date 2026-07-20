theory Test_BatchCase1Reject
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.BatchCase1Reject"]]

lemma t1: "(x::int) * x \<ge> 0"
  by aoa

end
