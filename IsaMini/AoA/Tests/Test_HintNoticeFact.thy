theory Test_HintNoticeFact
  imports Complex_Main Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.HintNoticeFact"]]

(* Test-only entry (conjI is not a real production hint): exercises the fact
   NOTICE path (op proceeds, note surfaced once per session). *)
declare conjI [agent_notice "conjI is registered as a noticed fact for this test; proceeding."]

lemma hint_notice_fact: "(x::int) * x \<ge> 0"
  by   aoa

end
