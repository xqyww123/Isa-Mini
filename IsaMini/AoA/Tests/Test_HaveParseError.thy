theory Test_HaveParseError
  imports Complex_Main Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.HaveParseError"]]

(* log-2: a malformed Have conclusion must get a precise marked-token message. *)
lemma have_parse_error_test: "(x::int) * x \<ge> 0"
  by Agent AoA

end
