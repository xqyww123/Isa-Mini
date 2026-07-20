theory Test_CollectionGate
  imports Complex_Main Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.SemanticKNN_collection_gate"]]

lemma collection_gate_test: "(x::real) = x"
  by aoa

end
