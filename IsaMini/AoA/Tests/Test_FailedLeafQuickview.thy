theory Test_FailedLeafQuickview
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.FailedLeafQuickview"]]

lemma "(x::int) * x \<ge> 0"
  by   aoa

end
