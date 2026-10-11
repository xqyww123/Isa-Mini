theory Test_Tactic1
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Tactic1"]]
declare [[AoA_tactics add: induction \<open>prove by induction on a variable\<close> shown_in: prompt
                           simp \<open>rewrite the goal with the simplifier\<close>]]

lemma t1: "rev (rev xs) = xs"
  by aoa

end
