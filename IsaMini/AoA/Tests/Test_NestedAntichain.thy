theory Test_NestedAntichain
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.NestedAntichain"]]

(* Distinctive goal, left unfinished by the test, to avoid the shared proof cache *)
lemma nested_antichain_test: "(0::int) \<le> x * x + (19::int)"
  by Agent AoA

end
