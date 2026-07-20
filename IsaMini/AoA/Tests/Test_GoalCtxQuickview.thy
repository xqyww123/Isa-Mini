theory Test_GoalCtxQuickview
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.GoalCtxQuickview"]]

lemma "\<forall>x::nat. P x \<and> Q x"
  by  aoa

end
