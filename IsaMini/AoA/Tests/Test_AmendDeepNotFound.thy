theory Test_AmendDeepNotFound
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.AmendDeepNotFound"]]

lemma t1:
  fixes x :: "int"
  assumes h: "x \<ge> 0"
  shows "x * x \<ge> 0"
  by aoa

end
