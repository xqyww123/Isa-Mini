theory Test_FactByNameWhereOF
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.FactByNameWhereOF"]]

lemma factbyname_whereof_test:
  assumes rule: "\<forall>x::nat. S x \<longrightarrow> R x" and hs: "S (7::nat)"
  shows "R (7::nat)"
  by aoa

end
