theory Test_AbbrevQuery
  imports Complex_Main Minilang_AoA.Minilang_AoA
begin

abbreviation my_true :: bool where
  "my_true \<equiv> True"

declare [[AoA_driver="test.AbbrevQuery"]]

lemma abbrev_query_test: "even (n::nat) \<Longrightarrow> n mod 2 = 0"
  by  aoa

end
