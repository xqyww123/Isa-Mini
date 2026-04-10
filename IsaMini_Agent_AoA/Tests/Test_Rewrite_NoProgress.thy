theory Test_Rewrite_NoProgress
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.Rewrite_NoProgress"]]

definition "foo \<equiv> (0::nat) = 0"

lemma rewrite_no_progress_test:
  assumes h1: "P (x::nat)"
      and h2: "Q (y::nat)"
  shows "P x \<and> Q y"
  by   aoa

end
