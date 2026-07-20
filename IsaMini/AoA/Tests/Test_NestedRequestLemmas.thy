theory Test_NestedRequestLemmas
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.NestedRequestLemmas"]]

(* Distinctive goal, left unfinished by the test, to avoid the shared proof cache *)
lemma nested_request_lemmas_test: "(0::int) \<le> x * x + (13::int)"
  by Agent AoA

end
