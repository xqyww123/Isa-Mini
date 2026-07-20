theory Test_RequestLemmasAutoProve
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.RequestLemmasAutoProve"]]

lemma test_request_lemmas_auto_prove:
  shows "(0::nat) \<le> n"
  by aoa

end
