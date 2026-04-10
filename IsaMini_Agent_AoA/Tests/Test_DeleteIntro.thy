theory Test_DeleteIntro
  imports Minilang_Agent.Minilang_Agent
begin

setup \<open>Config.put_global Minilang.INTRO_split_conj true\<close>

lemma conj_test:
  assumes "P" and "Q" and "R"
  shows "P \<and> Q \<and> R"
  by   aoa

end
