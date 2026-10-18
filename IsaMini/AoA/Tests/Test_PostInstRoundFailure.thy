theory Test_PostInstRoundFailure
  imports Minilang_AoA.Minilang_AoA
begin

declare [[AoA_driver="test.PostInstRoundFailure"]]
declare [[AoA_tactics rule \<open>apply an introduction rule\<close>]]

consts PP :: "nat \<Rightarrow> bool"
consts QQ :: "nat \<Rightarrow> bool"
lemma p0: "PP 0" sorry
lemma q0: "QQ 0" sorry

lemma t5: "\<exists>x. PP x \<and> QQ x"
  by aoa

end
