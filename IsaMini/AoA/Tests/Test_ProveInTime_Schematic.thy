theory Test_ProveInTime_Schematic
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.ProveInTime_Schematic"]]

lemma schematic_pit_test: "(x::int) * x \<ge> 0"
  by    aoa

end
