theory Test_Suffices
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Suffices"]]

(* Test: Prove x^2 >= 0 by showing x^2 + 1 > 0 suffices *)
lemma suffices_test1: "(x::int) * x \<ge> 0"
  by   aoa

ML \<open>Par_Exn.release_first\<close>

end
