theory Test_GoalCtxQuickview
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.GoalCtxQuickview"]]

lemma "\<forall>x::nat. P x \<and> Q x"
  by  aoa

end
