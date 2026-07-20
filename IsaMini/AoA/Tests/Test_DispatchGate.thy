theory Test_DispatchGate
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.DispatchGate"]]

(* Distinctive goal, left unfinished by the test, to avoid the shared proof cache *)
lemma dispatch_gate_test: "(0::int) \<le> x * x + (5::int)"
  by Agent AoA

end
