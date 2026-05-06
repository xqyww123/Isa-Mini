theory Test_SemanticKNN_theories_include
  imports Complex_Main Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.SemanticKNN_theories_include"]]

lemma "length (xs @ ys) = length xs + length ys"
  by  aoa

end
