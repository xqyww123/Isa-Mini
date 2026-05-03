theory Test_CaseSplit_NestedCaseNameShadow
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.CaseSplit_NestedCaseNameShadow"]]

lemma t_nested: "P (n::nat)"
  by aoa

end
