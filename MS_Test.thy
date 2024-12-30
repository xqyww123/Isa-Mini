theory MS_Test
  imports Main Proof_Shell
begin

lemma \<open>0 < length x \<Longrightarrow> x \<noteq> []\<close>
  by (min_script \<open>CASE_SPLIT x PRINT END\<close>)

lemma \<open>rev (rev l) = l\<close>
  by (min_script \<open>END\<close>)

lemma \<open>rev (rev l) = l\<close>
  by (min_script \<open>INDUCT l PRINT END\<close>)

        
lemma  
  \<open> \<And>a. A \<and> B \<Longrightarrow> \<forall>x. P x \<Longrightarrow> P a \<and> A\<close>
  by (min_script \<open>END\<close>)
 
lemma  
  \<open> \<And>a. A \<and> B \<Longrightarrow> \<forall>x. P x \<Longrightarrow> P a \<and> A\<close>
  by (min_script \<open>INTROS HAVE "A" PRINT END END\<close>)

lemma  
  \<open> \<And>a y. A \<and> B \<Longrightarrow> \<forall>x. P x \<Longrightarrow> P a \<and> A\<close>
  by (min_script \<open>INTROS CRUSH PRINT HAVE "A" END PRINT HAMMER PRINT END\<close>)

lemma  
  \<open> \<And>a. A \<and> B \<Longrightarrow> \<forall>x. P x \<Longrightarrow> P a \<and> B\<close>
  by (min_script \<open>PRINT INTROS END\<close>)

        
lemma   
  \<open> \<And>y. A \<and> B \<Longrightarrow> \<forall>x. P x \<Longrightarrow> P y \<and> B\<close>
  by (min_script \<open>
  INTROS
  obtain x :: int and z :: nat where "0 < x" and c: "2 < z" and "1 < x" PRINT end PRINT end\<close>)


end