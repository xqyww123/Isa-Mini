theory Test_Contradiction_double_neg
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.Contradiction_double_neg"]]

lemma "\<not> \<not> True"
  by aoa

end
