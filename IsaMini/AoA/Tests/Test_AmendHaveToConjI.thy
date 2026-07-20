theory Test_AmendHaveToConjI
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.AmendHaveToConjI"]]

lemma "True \<and> True"
  by Agent AoA

end
