theory Test_Tactic6
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Tactic6"]]
declare [[AoA_tactics simp \<open>rewrite the goal with the simplifier\<close>]]

lemma t6: "x + 0 = (x::nat)"
  by aoa

end
