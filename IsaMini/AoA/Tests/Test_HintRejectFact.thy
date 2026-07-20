theory Test_HintRejectFact
  imports Complex_Main Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.HintRejectFact"]]

(* Test-only entry (refl is not a real production hint): exercises the fact
   REJECT path. *)
declare refl [agent_reject "refl is registered as a rejected fact for this test; do not reference it."]

lemma hint_reject_fact: "(x::int) * x \<ge> 0"
  by   aoa

end
