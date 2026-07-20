theory Test_IntroObvious
  imports Minilang_Agent.Minilang_Agent
begin

declare [[AoA_driver="test.IntroObvious"]]

lemma conj_test:
  assumes "P" and "Q" and "R"
  shows "P \<and> Q \<and> R"
  by aoa


lemma \<open>True \<and> True\<close>
  apply (min_script \<open>
  SPLIT_CONJS
  SIMP
  NEXT
  SIMP
  END
\<close>)
  done

end
