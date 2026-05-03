theory Structured_Statement_Test
  imports Main Minilang.Minilang
begin

declare [[working_mode = STRICT]]

section \<open>Backward compat: bare SUFFICES still works\<close>

lemma "A \<and> B \<Longrightarrow> B \<and> A"
  by (min_script \<open>
    SUFFICES "B \<and> A"
      END
    RULE NEXT END
  \<close>)

section \<open>SUFFICES with for\<close>

lemma "\<forall>x::nat. x \<le> x"
  by (min_script \<open>
    SUFFICES "x \<le> x" for x :: nat
      END
    END
  \<close>)

section \<open>SUFFICES with if\<close>

lemma "A \<and> B \<longrightarrow> B \<and> A"
  by (min_script \<open>
    SUFFICES "B \<and> A" if "A \<and> B"
      END
    END
  \<close>)

section \<open>SUFFICES with if and for\<close>

lemma "\<forall>x::nat. x > 0 \<longrightarrow> x \<ge> 1"
  by (min_script \<open>
    SUFFICES "x \<ge> 1" if "x > 0" for x :: nat
      END
    END
  \<close>)

section \<open>SUFFICES with multiple premises\<close>

lemma "A \<longrightarrow> B \<longrightarrow> A \<and> B"
  by (min_script \<open>
    SUFFICES "A \<and> B" if "A" and "B"
      END
    END
  \<close>)

end
