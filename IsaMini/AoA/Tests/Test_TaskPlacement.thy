theory Test_TaskPlacement
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.TaskPlacement"]]

lemma tp: "(1::nat) \<le> 2"
  by aoa

end
