theory Test_InstUndeclared
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.InstUndeclared"]]

lemma inst_undeclared_test:
  assumes h1: "P (0::nat)"
      and h2: "\<forall>x::nat. P x \<longrightarrow> Q x"
  shows "Q (0::nat)"
  by  aoa

end
