theory Test_HintRejectConst
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.HintRejectConst"]]

declare [[agent_reject_constant Rat.of_int
  "Rat.of_int is a code-generation shadow constant that the of_int_* lemmas do not apply to. Use rat_of_int instead."]]

lemma hint_reject_const: "(x::int) * x \<ge> 0"
  by   aoa

end
