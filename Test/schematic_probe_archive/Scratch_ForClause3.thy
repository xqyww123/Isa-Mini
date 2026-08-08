theory Scratch_ForClause3
  imports Main Minilang.Minilang
begin

declare [[working_mode = STRICT]]

section \<open>H: HAVE with le op\<close>

lemma "(0::nat) \<le> 1"
  by (min_script \<open>
    HAVE "(0::nat) \<le> 1"
      END
    END
  \<close>)

end
