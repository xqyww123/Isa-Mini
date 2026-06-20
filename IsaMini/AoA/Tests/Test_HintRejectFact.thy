theory Test_HintRejectFact
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.HintRejectFact"]]

(* DRAFT message text — final wording pending user sign-off. *)
declare refl [agent_reject "DRAFT: refl is registered as a rejected fact for this test; do not reference it."]

lemma hint_reject_fact: "(x::int) * x \<ge> 0"
  by   aoa

end
