theory Test_InstUndeclared
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.InstUndeclared"]]

lemma inst_undeclared_test:
  assumes h1: "P (0::nat)"
      and h2: "\<forall>x::nat. P x \<longrightarrow> Q x"
  shows "Q (0::nat)"
  by  aoa

end
