theory Test_IdInTextRegex
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.IdInTextRegex"]]

(* Distinctive goal, left unfinished by the test, to avoid the shared proof cache *)
lemma id_in_text_regex_test: "(0::int) \<le> x * x + (23::int)"
  by Agent AoA

end
