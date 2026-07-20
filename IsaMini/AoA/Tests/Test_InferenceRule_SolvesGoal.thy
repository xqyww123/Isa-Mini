theory Test_InferenceRule_SolvesGoal
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.InferenceRuleSolvesGoal"]]

lemma "(a :: nat) = a"
  by  a oa


function zs where
  "zs a b n = (if n = (0::nat) then (0::nat) else if n < b then b + zs (1::nat) (2::nat) (n - a) else zs b (a + b) n)"
  by auto

termination sorry

thm zs.simps
lemma "P (zs x y z)"
  apply (subst zs.simps)

end
