theory MS_Test
  imports Main Proof_Shell
begin

lemma \<open>0 < length x \<Longrightarrow> x \<noteq> []\<close>
  by (min_script \<open>CASE_SPLIT x PRINT END\<close>)

lemma \<open>rev (rev l) = l\<close>
  by (min_script \<open>END\<close>)

lemma \<open>rev (rev l) = l\<close>
  by (min_script \<open>INDUCT l PRINT END\<close>)

end