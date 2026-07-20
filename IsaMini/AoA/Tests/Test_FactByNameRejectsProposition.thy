theory Test_FactByNameRejectsProposition
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.FactByNameRejectsProposition"]]

lemma factbyname_rejects_proposition_test:
  fixes k :: nat
  shows "(GREATEST k1. k1 \<le> k) = k"
  by aoa

end
