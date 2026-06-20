theory Test_HintRejectConst
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.HintRejectConst"]]

(* DRAFT message text — final wording pending user sign-off. *)
declare [[agent_reject_constant Rat.of_int
  "DRAFT: Rat.of_int is a code-generation constant distinct from the coercion rat_of_int; of_int_* lemmas do not apply to it. Use rat_of_int instead."]]

lemma hint_reject_const: "(x::int) * x \<ge> 0"
  by   aoa

end
