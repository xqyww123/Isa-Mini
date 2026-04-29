theory Test_CaseSplit_NestedSkolem
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.CaseSplit_NestedSkolem"]]

lemma nested_nat_casesplit: "P (n::nat) (m::nat)"
  by aoa

end
