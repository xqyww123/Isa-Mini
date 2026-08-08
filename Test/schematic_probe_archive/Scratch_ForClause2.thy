theory Scratch_ForClause2
  imports Main Minilang.Minilang
begin

declare [[working_mode = STRICT]]

section \<open>A: equality op, for only\<close>

lemma "\<forall>x::nat. x = x"
  by (min_script \<open>
    SUFFICES "x = x" for x :: nat
      END
    END
  \<close>)

section \<open>B: le op, if and for\<close>

lemma "\<forall>x::nat. x > 0 \<longrightarrow> x \<le> x"
  by (min_script \<open>
    SUFFICES "x \<le> x" if pos: "x > 0" for x :: nat
      END
    END WITH pos
  \<close>)

section \<open>C: le op, for without type annotation\<close>

lemma "\<forall>x::nat. x \<le> x"
  by (min_script \<open>
    SUFFICES "x \<le> x" for x
      END
    END
  \<close>)

section \<open>E: le op, different sides, for only\<close>

lemma "\<forall>x::nat. x \<le> Suc x"
  by (min_script \<open>
    SUFFICES "x \<le> Suc x" for x :: nat
      END
    END
  \<close>)

section \<open>F: less op, for only\<close>

lemma "\<forall>x::nat. x < Suc x"
  by (min_script \<open>
    SUFFICES "x < Suc x" for x :: nat
      END
    END
  \<close>)

section \<open>G: le op, bare SUFFICES after INTRO\<close>

lemma "\<forall>x::nat. x \<le> x"
  by (min_script \<open>
    INTRO
    SUFFICES "x \<le> x"
      END
    END
  \<close>)

end
