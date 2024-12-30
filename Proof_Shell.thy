text \<open>Driven by AI purely and only.\<close>

theory Proof_Shell
  imports HOL.HOL Auto_Sledgehammer.Auto_Sledgehammer
begin

thm exE

definition Ex   where \<open>Ex   \<equiv> HOL.Ex\<close>
definition disj where \<open>disj \<equiv> HOL.disj\<close>
definition conj where \<open>conj \<equiv> HOL.conj\<close>

lemma XX:
  \<open>Ex (\<lambda>x. P x) \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q) \<Longrightarrow> Q\<close>
  unfolding Ex_def
  by blast

declare [[ML_debugger]]

ML_file \<open>./library/proof.ML\<close>

hide_const Ex conj disj
        
lemma  
  \<open> \<And>a. A \<and> B \<Longrightarrow> \<forall>x. P x \<Longrightarrow> P a \<and> A\<close>
  by (min_script \<open>END\<close>)
 
lemma  
  \<open> \<And>a. A \<and> B \<Longrightarrow> \<forall>x. P x \<Longrightarrow> P a \<and> A\<close>
  by (min_script \<open>INTROS HAVE "A" PRINT END END\<close>)

lemma  
  \<open> \<And>a. A \<and> B \<Longrightarrow> \<forall>x. P x \<Longrightarrow> P a \<and> A\<close>
  by (min_script \<open>INTROS CRUSH PRINT HAVE "A" END PRINT HAMMER PRINT END\<close>)

lemma  
  \<open> \<And>a. A \<and> B \<Longrightarrow> \<forall>x. P x \<Longrightarrow> P a \<and> B\<close>
  by (min_script \<open>PRINT INTROS END\<close>)


notepad
begin

  fix x :: int

  assume A: \<open>0 < x\<close>

  fix x :: int
assume B: \<open>0 < x\<close>
  thm A
  ML_val \<open>Thm.prop_of @{thm A} |> (fn _ $ (_ $ X) => X)\<close>
  ML_val \<open>Variable.revert_fixed \<^context> "x__"\<close>
ML_val \<open>Thm.prop_of @{thm B}\<close>

end

end