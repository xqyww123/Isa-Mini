theory Test_AbbrevQuery
  imports Complex_Main Minilang_Agent.Minilang_Agent
begin

abbreviation my_true :: bool where
  "my_true \<equiv> True"

declare [[agent_AoA_driver="test.AbbrevQuery"]]

lemma abbrev_query_test: "even (n::nat) \<Longrightarrow> n mod 2 = 0"
  by  aoa

end
