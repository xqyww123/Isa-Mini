theory Test_Induction_AutoIntroBoundVar
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Induction_AutoIntroBoundVar"]]

lemma t: "(x::int) * x \<ge> 0"
  by aoa

end
