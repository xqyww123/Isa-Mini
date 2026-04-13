theory Chaining_Test
  imports Main Minilang.Minilang
begin

(* Tests for the CHAINING command: chain a sequence of already-bound facts
   via registered transitivity rules into a single named derived fact. *)

declare [[working_mode = STRICT]]

(* --- Basic equality chain: two facts -------------------------------------- *)

lemma
  fixes a b c :: nat
  assumes ab: "a = b" and bc: "b = c"
  shows "a = c"
  by (min_script \<open>
    CHAINING ac WITH ab bc
    PRINT
    END WITH ac
  \<close>)

(* --- Equality chain: three facts ------------------------------------------ *)

lemma
  fixes a b c d :: nat
  assumes ab: "a = b" and bc: "b = c" and cd: "c = d"
  shows "a = d"
  by (min_script \<open>
    CHAINING ad WITH ab bc cd
    PRINT
    END WITH ad
  \<close>)

(* --- Mixed operators: = and \<le>  \<Longrightarrow>  \<le> --------------------------------- *)

lemma
  fixes a b c :: nat
  assumes ab: "a = b" and bc: "b \<le> c"
  shows "a \<le> c"
  by (min_script \<open>
    CHAINING ac WITH ab bc
    PRINT
    END WITH ac
  \<close>)

(* --- Mixed operators: \<le> and < \<Longrightarrow> < ---------------------------------- *)

lemma
  fixes a b c :: nat
  assumes ab: "a \<le> b" and bc: "b < c"
  shows "a < c"
  by (min_script \<open>
    CHAINING ac WITH ab bc
    END WITH ac
  \<close>)

(* --- Mixed operators: four-fact chain ------------------------------------- *)

lemma
  fixes a b c d e :: nat
  assumes ab: "a = b" and bc: "b \<le> c" and cd: "c < d" and de: "d = e"
  shows "a < e"
  by (min_script \<open>
    CHAINING ae WITH ab bc cd de
    END WITH ae
  \<close>)

(* --- Set-inclusion chain (\<subseteq>) --------------------------------------- *)

lemma
  fixes A B C :: "nat set"
  assumes AB: "A \<subseteq> B" and BC: "B \<subseteq> C"
  shows "A \<subseteq> C"
  by (min_script \<open>
    CHAINING AC WITH AB BC
    END WITH AC
  \<close>)

(* --- The chained fact is usable as an ordinary local fact ----------------- *)

lemma
  fixes a b c :: nat
  assumes ab: "a = b" and bc: "b = c"
  shows "f a = f c"
  by (min_script \<open>
    CHAINING ac WITH ab bc
    END WITH ac
  \<close>)

(* --- Chained fact can be passed to another CHAINING ---------------------- *)

lemma
  fixes a b c d e :: nat
  assumes ab: "a = b" and bc: "b = c" and cd: "c \<le> d" and de: "d = e"
  shows "a \<le> e"
  by (min_script \<open>
    CHAINING ac WITH ab bc
    CHAINING ae WITH ac cd de
    END WITH ae
  \<close>)

end
