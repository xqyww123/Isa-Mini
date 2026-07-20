theory Test_ObviousTimeout2
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.ObviousTimeout_default"]]

lemma obvious_timeout_test2: "True"
  by aoa

end
