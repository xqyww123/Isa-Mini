theory Test_CollectionGate
  imports Complex_Main Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.SemanticKNN_collection_gate"]]

lemma collection_gate_test: "(x::real) = x"
  by aoa

end
