theory Test_RequestLemmasAutoProve
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.RequestLemmasAutoProve"]]

lemma test_request_lemmas_auto_prove:
  shows "(0::nat) \<le> n"
  by aoa

end
