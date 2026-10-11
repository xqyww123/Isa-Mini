theory Test_Tactic4
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.Tactic4"]]
declare [[AoA_tactics simp \<open>rewrite the goal with the simplifier\<close>
                       rule \<open>apply an introduction rule\<close>]]

lemma t4: "x + 0 = (x::nat)"
  by aoa

end
