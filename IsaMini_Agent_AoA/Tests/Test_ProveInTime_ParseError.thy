theory Test_ProveInTime_ParseError
  imports Minilang_Agent.Minilang_Agent
begin

lemma suffices_test1: "(x::int) * x \<ge> 0"
  by    AgentAoA

end
