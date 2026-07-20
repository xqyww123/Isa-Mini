theory Test_CaseSplit_NestedSkolem
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.CaseSplit_NestedSkolem"]]

lemma nested_nat_casesplit: "P (n::nat) (m::nat)"
  by aoa

end
