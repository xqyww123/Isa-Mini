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

section \<open>SUFFICES with for only\<close>

lemma "\<forall>x::nat. x \<le> x"
  by (min_script \<open>
    SUFFICES "x \<le> x" for x :: nat
      END
    END
  \<close>)

section \<open>SUFFICES with if only: premise accessible by name\<close>

lemma "A \<and> B \<longrightarrow> B \<and> A"
  by (min_script \<open>
    SUFFICES "B \<and> A" if h: "A \<and> B"
      END
    END WITH h
  \<close>)

section \<open>SUFFICES with if and for\<close>

lemma "\<forall>x::nat. x > 0 \<longrightarrow> x \<ge> Suc 0"
  by (min_script \<open>
    SUFFICES "x \<ge> Suc 0" if pos: "x > 0" for x :: nat
      END
    END WITH pos
  \<close>)

section \<open>SUFFICES with multiple named premises\<close>

lemma "A \<longrightarrow> B \<longrightarrow> A \<and> B"
  by (min_script \<open>
    SUFFICES "A \<and> B" if h1: "A" and h2: "B"
      END
    END WITH h1 h2
  \<close>)

section \<open>SUFFICES with unnamed premises (auto-named)\<close>

lemma "A \<longrightarrow> B \<longrightarrow> A \<and> B"
  by (min_script \<open>
    SUFFICES "A \<and> B" if "A" and "B"
      END
    END WITH assm0 assm1
  \<close>)

section \<open>SUFFICES with multiple for variables\<close>

lemma "\<forall>(x::nat) (y::nat). x + y = y + x"
  by (min_script \<open>
    SUFFICES "x + y = y + x" for x :: nat and y :: nat
      END
    END
  \<close>)

section \<open>SUFFICES with and-connected shows\<close>

lemma "A \<longrightarrow> A \<and> A"
  by (min_script \<open>
    SUFFICES "A" and "A" if h: "A"
      END
    END WITH h
  \<close>)

section \<open>SUFFICES bare inside a nested proof\<close>

lemma "A \<Longrightarrow> B \<Longrightarrow> A \<and> B"
  by (min_script \<open>
    SUFFICES "A \<and> B"
      END
    RULE NEXT END
  \<close>)

end
