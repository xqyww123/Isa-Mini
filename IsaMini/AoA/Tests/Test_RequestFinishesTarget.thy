theory Test_RequestFinishesTarget
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.RequestFinishesTarget"]]

lemma test_request_finishes_target:
  shows "(0::nat) \<le> n"
  by aoa

end
