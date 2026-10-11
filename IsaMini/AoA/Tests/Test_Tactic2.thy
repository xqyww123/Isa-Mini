theory Test_Tactic2
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Tactic2"]]
declare [[AoA_tactics simp \<open>rewrite the goal with the simplifier\<close>]]

lemma t2: "x + 0 = (x::nat)"
  by aoa

end
