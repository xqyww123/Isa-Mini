theory Test_SemanticKNN_induction_rule
  imports Complex_Main Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.SemanticKNN_induction_rule"]]

lemma "(n::nat) + 0 = n"
  by  aoa

end
