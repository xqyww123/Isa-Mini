theory Test_IntroObvious
  imports Minilang_Agent.Minilang_Agent
begin

declare [[agent_AoA_driver="test.DeleteIntro"]]

lemma conj_test:
  assumes "P" and "Q" and "R"
  shows "P \<and> Q \<and> R"
  by Agen tAoA


lemma \<open>True \<and> True\<close>
  apply (min_script \<open>
  SPLIT_CONJS
  NEXT NEXT END
\<close>)

end
