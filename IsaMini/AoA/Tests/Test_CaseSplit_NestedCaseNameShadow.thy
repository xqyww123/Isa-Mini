theory Test_CaseSplit_NestedCaseNameShadow
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.CaseSplit_NestedCaseNameShadow"]]

lemma t_nested: "P (n::nat)"
  by aoa

end
