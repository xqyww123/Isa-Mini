theory Test_AddConstraints
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.AddConstraints"]]

lemma addconstraints_test: "(x::int) * x \<ge> 0"
  by Agent AoA

end
