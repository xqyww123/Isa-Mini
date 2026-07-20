theory Test_ProveInTime_ParseError
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.ProveInTime_ParseError"]]

lemma suffices_test1: "(x::int) * x \<ge> 0"
  by    aoa

end
