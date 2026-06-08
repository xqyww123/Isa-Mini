theory Test_SemanticKNN_UnequalLengths
  imports Complex_Main Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.SemanticKNN_UnequalLengths"]]

lemma "(n::nat) + 0 = n"
  by  aoa

end
