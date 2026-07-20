theory Test_DeleteOneOfThreeCases
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.DeleteOneOfThreeCases"]]

lemma t1: "(0::nat) = 0 \<and> (1::nat) = 1 \<and> (P::nat\<Rightarrow>bool) 0"
  by  aoa

end
