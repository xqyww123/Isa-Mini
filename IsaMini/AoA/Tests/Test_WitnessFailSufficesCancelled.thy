theory Test_WitnessFailSufficesCancelled
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.WitnessFailSufficesCancelledFill"]]

lemma wfsc: "(x::int) * x \<ge> 0"
  by   aoa

end
