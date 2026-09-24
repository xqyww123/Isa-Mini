theory Test_ReadMemoryGate
  imports Complex_Main Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.ReadMemoryGate"]]

lemma t1: "(1::real) \<le> 2"
  by   aoa

end
