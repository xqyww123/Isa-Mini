theory Test_Induction_IllTypedBoundVar
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Induction_IllTypedBoundVar"]]

lemma t: "(x::int) * x \<ge> 0"
  by aoa

end
