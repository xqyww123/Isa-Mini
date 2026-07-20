theory Test_Branch
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Branch1"]]

lemma t1: "(x::int) * x \<ge> 0"
  by   aoa

end