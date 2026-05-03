theory Test_Rewrite_Targeted_Where imports
  Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Rewrite_Targeted_Where"]]

axiomatization where
  my_looping: "(\<exists>n::nat. P n) = (\<exists>n. P n \<and> True)"

lemma targeted_where_test:
  assumes h: "\<exists>n::nat. n > 0"
  shows "\<exists>n::nat. n > 0 \<and> True"
  by aoa

end
