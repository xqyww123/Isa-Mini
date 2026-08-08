theory Scratch_ForClause1
  imports Main Minilang.Minilang
begin

declare [[working_mode = STRICT]]

section \<open>Probe 1: SUFFICES with for only\<close>

lemma "\<forall>x::nat. x \<le> x"
  by (min_script \<open>
    SUFFICES "x \<le> x" for x :: nat
      END
    END
  \<close>)

section \<open>Probe 2: SUFFICES with if and for\<close>

lemma "\<forall>x::nat. x > 0 \<longrightarrow> x \<ge> Suc 0"
  by (min_script \<open>
    SUFFICES "x \<ge> Suc 0" if pos: "x > 0" for x :: nat
      END
    END WITH pos
  \<close>)

section \<open>Probe 3: SUFFICES with multiple for variables\<close>

lemma "\<forall>(x::nat) (y::nat). x + y = y + x"
  by (min_script \<open>
    SUFFICES "x + y = y + x" for x :: nat and y :: nat
      END
    END
  \<close>)

end
