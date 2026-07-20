theory Test_HintNoticeConst
  imports Complex_Main Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.HintNoticeConst"]]

(* Same const/message as the reject seed, but registered as a NOTICE (severity
   flag flipped): the op proceeds and the note is surfaced once per session. *)
declare [[agent_notice_constant Rat.of_int
  "Rat.of_int is a code-generation shadow constant that the of_int_* lemmas do not apply to. Use rat_of_int instead."]]

lemma hint_notice_const: "(x::int) * x \<ge> 0"
  by   aoa

end
