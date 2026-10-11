theory Test_TacticPrompt
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.TacticPrompt"]]
declare [[AoA_tactics simp \<open>rewrite the goal with the simplifier,
    e.g. \<open>a \<Longrightarrow> b\<close>   becomes
  what the rules give\<close> shown_in: prompt]]

lemma tp: "(1::nat) \<le> 2"
  by aoa

end
