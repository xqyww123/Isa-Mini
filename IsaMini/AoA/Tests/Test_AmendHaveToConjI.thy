theory Test_AmendHaveToConjI
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.AmendHaveToConjI"]]

lemma "True \<and> True"
  by Agent AoA

end
