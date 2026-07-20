theory Test_FailedLeafQuickview
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.FailedLeafQuickview"]]

lemma "(x::int) * x \<ge> 0"
  by   aoa

end
