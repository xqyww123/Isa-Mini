theory Proof_Shell
  imports HOL.HOL
begin

thm exE

definition Ex   where \<open>Ex   \<equiv> HOL.Ex\<close>
definition conj where \<open>conj \<equiv> HOL.conj\<close>

lemma XX:
  \<open>Ex (\<lambda>x. P x) \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q) \<Longrightarrow> Q\<close>
  unfolding Ex_def
  by blast

ML_file \<open>./library/proof.ML\<close>

hide_const Ex Conj

end