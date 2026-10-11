theory Test_TacticSync
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.TacticSync"]]
declare [[AoA_tactics simp \<open>rewrite the goal with the simplifier\<close>]]

lemma ts: "(1::nat) \<le> 2"
  by aoa

end
