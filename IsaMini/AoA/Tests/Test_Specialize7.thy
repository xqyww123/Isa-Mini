theory Test_Specialize7
  imports Complex_Main Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Derive7"]]

text \<open>Test diagnostic error messages from SPECIALIZE.
  h1 has type nat, but mult_mod_cancel_left requires euclidean_ring_cancel.
  h3 has head symbol "plus" which clashes with "times" in the rule premise.\<close>

lemma specialize_test7:
  assumes h1: "(x::nat) mod q = y mod q"
      and h2: "coprime q (2::nat)"
      and h3: "(x::int) + y = z"
  shows "x mod q = y mod q"
  by  aoa

end
