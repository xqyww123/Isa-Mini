theory Test_DeleteCaseHole
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.DeleteCaseHole"]]

lemma t1: "(0::nat) = 0 \<and> (P::nat\<Rightarrow>bool) 0"
  by  aoa

end
