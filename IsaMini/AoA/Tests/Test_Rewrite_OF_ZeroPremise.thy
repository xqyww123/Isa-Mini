theory Test_Rewrite_OF_ZeroPremise
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Rewrite_OF_ZeroPremise"]]

lemma of_zero_premise_test:
  assumes h1: "y = x + (0::int)"
  shows "x + 0 = y"
  by aoa

end
