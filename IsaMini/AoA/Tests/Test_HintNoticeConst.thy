theory Test_HintNoticeConst
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.HintNoticeConst"]]

(* DRAFT message text — final wording pending user sign-off. A NOTICE does not
   block the operation; it is surfaced once per session per registered name. *)
declare [[agent_notice_constant Rat.of_int
  "DRAFT: you wrote Rat.of_int; the coercion is rat_of_int. Proceeding, but prefer rat_of_int."]]

lemma hint_notice_const: "(x::int) * x \<ge> 0"
  by   aoa

end
