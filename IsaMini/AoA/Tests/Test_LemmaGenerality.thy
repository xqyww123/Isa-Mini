theory Test_LemmaGenerality
  imports Complex_Main Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.LemmaGenerality"]]

lemma test_lemma_generality:
  shows "(0::nat) \<le> n"
  by aoa

end
