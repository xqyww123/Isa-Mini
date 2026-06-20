theory Test_HintNoticeFact
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.HintNoticeFact"]]

(* DRAFT message text — final wording pending user sign-off. A NOTICE does not
   block the operation; it is surfaced once per session per registered name. *)
declare conjI [agent_notice "DRAFT: conjI is registered as a noticed fact for this test; proceeding."]

lemma hint_notice_fact: "(x::int) * x \<ge> 0"
  by   aoa

end
