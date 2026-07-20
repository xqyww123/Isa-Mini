theory Test_RenameFactNotFound
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.RenameFactNotFound"]]

lemma assumes h1: "(x::int) \<ge> 0" shows "x \<ge> 0"
  by   aoa

end
