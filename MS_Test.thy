theory MS_Test
  imports Main Proof_Shell HOL.Transcendental
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

lemma
  \<open> \<And>y. A \<and> B \<Longrightarrow> \<forall>x. P x \<Longrightarrow> P y \<and> B\<close>
  by (min_script \<open>
    INTROS
    RULE
    HAMMER
    RULE assm0(1)[THEN conjunct2]
    END
 \<close>)



theorem sqrt2_not_rational:
  "sqrt 2 \<notin> \<rat>"
by (min_script \<open>
  CRUSH
  OBTAIN m n :: nat where "\<bar>sqrt 2\<bar> = m / n" and "coprime m n" END
  HAVE "m^2 = (sqrt 2)^2 * n^2" END
  HAVE "m^2 = 2 * n^2" END
  HAVE "2 dvd m^2" END
  HAVE "2 dvd m" END
  HAVE "2 dvd n"
    OBTAIN k where "m = 2 * k" END
    HAVE "2 * n^2 = 2^2 * k^2" END
    HAVE "2 dvd n^2" END
    HAVE "2 dvd n" END
  END
  HAVE "2 dvd gcd m n" END
  HAVE "2 dvd 1" END
  END
\<close>)





end