theory Test_DeleteOneOfThreeCases
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.DeleteOneOfThreeCases"]]

lemma t1: "(0::nat) = 0 \<and> (1::nat) = 1 \<and> (P::nat\<Rightarrow>bool) 0"
  by  aoa

end
