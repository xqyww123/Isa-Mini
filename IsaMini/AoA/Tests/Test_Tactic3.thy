theory Test_Tactic3
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Tactic3"]]
declare [[AoA_tactics simp \<open>rewrite the goal with the simplifier\<close>]]

lemma t3: assumes h: "x = 1" shows "x + 1 = (2::nat)"
  by aoa

end
