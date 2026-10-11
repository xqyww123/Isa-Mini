theory Test_TacticQuery
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.TacticQuery"]]
declare [[AoA_tactics simp \<open>rewrite the goal with the simplifier\<close>
                       auto \<open>prove by classical reasoning and rewriting\<close> shown_in: prompt]]

lemma tq: assumes h: "x = 1" shows "x + 1 = (2::nat)"
  by aoa

end
