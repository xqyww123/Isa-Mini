theory Test_CaseSplit_Penetrate_Scratch
  imports Minilang.Minilang
begin

text \<open>Does CASE_SPLIT penetrate a leading object \<forall> and \<longrightarrow>?
      Goal has BOTH a leading \<forall>n and a premise n>0; we CASE_SPLIT on n
      WITHOUT any preceding INTRO.\<close>
lemma "\<forall>n::nat. n > 0 \<longrightarrow> n \<ge> 1"
  apply (min_script \<open>
  CASE_SPLIT "n"
  SIMP
  NEXT
  SIMP
  END
\<close>)
  done

text \<open>Same, but case-split on a boolean condition under the \<forall>/\<longrightarrow>.\<close>
lemma "\<forall>n::nat. n > 0 \<longrightarrow> (n = 1 \<or> n > 1)"
  apply (min_script \<open>
  CASE_SPLIT "n = 1"
  SIMP
  NEXT
  SIMP
  END
\<close>)
  done

end
