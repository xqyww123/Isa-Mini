theory Test_FactByNameWhere
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.FactByNameWhere"]]

lemma factbyname_where_test:
  assumes h: "\<forall>x::nat. P x"
  shows "P (0::nat)"
  by aoa

end
