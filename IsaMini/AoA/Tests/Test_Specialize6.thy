theory Test_Specialize6
  imports Complex_Main Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.Derive6"]]
declare [[unify_trace_failure, show_sorts]]
lemma specialize_test6:
  assumes h1: "(x::nat) mod q = y mod q"
      and h2: "coprime q (2::nat)"
    shows "x mod q = y mod q"
  thm mult_mod_cancel_left[OF _ h2]
  by ao

end
