theory Test_QuickviewCollapse
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.QuickviewCollapse"]]

lemma "(10::nat) > 0"
  by  aoa

end
