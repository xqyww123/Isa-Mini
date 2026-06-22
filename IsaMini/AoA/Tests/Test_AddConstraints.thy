theory Test_AddConstraints
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.AddConstraints"]]

lemma addconstraints_test: "(x::int) * x \<ge> 0"
  by Agent AoA

end
