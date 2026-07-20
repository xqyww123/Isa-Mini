theory Test_RequestFinishesTarget
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.RequestFinishesTarget"]]

lemma test_request_finishes_target:
  shows "(0::nat) \<le> n"
  by aoa

end
