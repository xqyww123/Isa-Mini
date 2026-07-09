theory Test_HintNoticeFact
  imports Complex_Main Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.HintNoticeFact"]]

(* Test-only entry (conjI is not a real production hint): exercises the fact
   NOTICE path (op proceeds, note surfaced once per session). *)
declare conjI [agent_notice "conjI is registered as a noticed fact for this test; proceeding."]

lemma hint_notice_fact: "(x::int) * x \<ge> 0"
  by   aoa

end
