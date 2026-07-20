theory Test_FactNameResolution
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.FactNameResolution"]]

lemma
  fixes x :: "nat"
  assumes h: "x > 2"
  shows "x > 0"
  by  aoa

end
