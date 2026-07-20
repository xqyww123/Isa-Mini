theory Test_HaveStructured
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.HaveStructured"]]

lemma "(3::nat) + 1 > 3"
  by aoa

end
