theory Test_HintRejectSetupRewriting
  imports Complex_Main Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.HintRejectSetupRewriting"]]

declare [[agent_reject_constant Rat.of_int
  "Rat.of_int is a code-generation shadow constant that the of_int_* lemmas do not apply to. Use rat_of_int instead."]]

lemma hint_reject_setup: "(x::int) * x \<ge> 0"
  by   aoa

end
