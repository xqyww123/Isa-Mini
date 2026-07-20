theory Test_MemorizeInteractionStages
  imports Complex_Main Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.MemorizeInteractionStages"]]

lemma t1: "(1::real) \<le> 2"
  by   aoa

end
