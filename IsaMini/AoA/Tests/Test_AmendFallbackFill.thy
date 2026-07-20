theory Test_AmendFallbackFill
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.AmendFallbackFill"]]

lemma t1:
  fixes x :: "int"
  assumes h: "x \<ge> 0"
  shows "x * x \<ge> 0"
  by aoa

end
