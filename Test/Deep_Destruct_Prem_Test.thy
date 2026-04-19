theory Deep_Destruct_Prem_Test
  imports Minilang.Minilang
begin

text \<open>Direct ML-level tests for @{ML Minilang.deep_destruct_prem} and
  @{ML Minilang.deep_destruct_term}. These exercise the destructuring
  rewrites in isolation, before the Python/Agent pipeline — so bugs in the
  Simplifier/simproc setup show up here rather than as a mysterious
  propagating exception.

  Each group prints one line with the group name, expected atom count,
  observed atom count, and the atoms themselves.\<close>

ML \<open>
local
  val ctxt = \<^context>

  fun show name expected_count (t : term) =
    let
      val atoms = Minilang.deep_destruct_term ctxt t
      val n = length atoms
      val status = if n = expected_count then "OK " else "FAIL "
      val _ = writeln (status ^ "[" ^ name ^ "] expected " ^
                       string_of_int expected_count ^ ", got " ^ string_of_int n)
      val _ = app (fn a => writeln ("    - " ^ Syntax.string_of_term ctxt a)) atoms
    in () end

  fun show_thm name expected_count (t : term) =
    let
      val prop = HOLogic.mk_Trueprop t
      val thm = Thm.assume (Thm.cterm_of ctxt prop)
      val atoms = Minilang.deep_destruct_prem ctxt thm
      val n = length atoms
      val status = if n = expected_count then "OK " else "FAIL "
      val _ = writeln (status ^ "[thm:" ^ name ^ "] expected " ^
                       string_of_int expected_count ^ ", got " ^ string_of_int n)
      val _ = app (fn a => writeln ("    - " ^ Syntax.string_of_term ctxt (Thm.prop_of a))) atoms
    in () end
in

val _ = writeln "=== deep_destruct_term (bool-level preview) ==="

(* 1. Plain right-associated conj *)
val _ = show "plain-conj" 3
  \<^term>\<open>(A::bool) \<and> B \<and> C\<close>

(* 2. ∀-conj: rewrite via all_conj_distrib, then split *)
val _ = show "all-conj" 2
  \<^term>\<open>\<forall>x. (P::'a \<Rightarrow> bool) x \<and> Q x\<close>

(* 3. ⟶-conj, small antecedent: rewrite via imp_conjR, then split *)
val _ = show "imp-conj-small" 2
  \<^term>\<open>(D::bool) \<longrightarrow> E \<and> F\<close>

(* 4. ⟶-conj, large antecedent (smart_size ≥ 20): size guard keeps intact *)
val _ = show "imp-conj-large" 1
  \<^term>\<open>((b1::bool) \<and> b2 \<and> b3 \<and> b4 \<and> b5 \<and>
          b6 \<and> b7 \<and> b8 \<and> b9 \<and> b10 \<and>
          b11 \<and> b12 \<and> b13 \<and> b14 \<and> b15 \<and>
          b16 \<and> b17 \<and> b18 \<and> b19 \<and> b20) \<longrightarrow> G \<and> H\<close>

(* 5. Non-destructible: plain HOL.implies with no conj RHS *)
val _ = show "non-destructible" 1
  \<^term>\<open>(X::bool) \<longrightarrow> Y\<close>

(* 6. Nested: ∀ and ⟶ combined *)
val _ = show "nested" 4
  \<^term>\<open>\<forall>x. ((A::'a \<Rightarrow> bool) x \<and> B x) \<and> ((D::bool) \<longrightarrow> E x \<and> F x)\<close>

val _ = writeln "=== deep_destruct_prem (thm-level, same semantics) ==="

val _ = show_thm "plain-conj" 3
  \<^term>\<open>(A::bool) \<and> B \<and> C\<close>
val _ = show_thm "all-conj" 2
  \<^term>\<open>\<forall>x. (P::'a \<Rightarrow> bool) x \<and> Q x\<close>
val _ = show_thm "imp-conj-small" 2
  \<^term>\<open>(D::bool) \<longrightarrow> E \<and> F\<close>
val _ = show_thm "imp-conj-large" 1
  \<^term>\<open>((b1::bool) \<and> b2 \<and> b3 \<and> b4 \<and> b5 \<and>
          b6 \<and> b7 \<and> b8 \<and> b9 \<and> b10 \<and>
          b11 \<and> b12 \<and> b13 \<and> b14 \<and> b15 \<and>
          b16 \<and> b17 \<and> b18 \<and> b19 \<and> b20) \<longrightarrow> G \<and> H\<close>

end
\<close>

text \<open>Regression: what the Python-side Intro flow actually calls on the
  premises of a lemma \<open>\<lbrakk>A \<and> B \<and> C; \<forall>x. P x \<and> Q x; D \<longrightarrow> E \<and> F; BIG \<longrightarrow> G \<and> H\<rbrakk> \<Longrightarrow> ...\<close>
  after \<open>strip_meta_and_hol_hhf\<close>. This is the exact input shape that was
  failing with a \<open>Trueprop :: bool \<Rightarrow> prop\<close> type error in the agent flow.\<close>

ML \<open>
local
  val ctxt = \<^context>
  (* Atomized goal form: HOL.implies chain under one outer Trueprop.
     strip_meta_and_hol_hhf would return the antecedents as bool terms. *)
  val prems : term list = [
    \<^term>\<open>(A::bool) \<and> B \<and> C\<close>,
    \<^term>\<open>\<forall>x. (P::'a \<Rightarrow> bool) x \<and> Q x\<close>,
    \<^term>\<open>(D::bool) \<longrightarrow> E \<and> F\<close>,
    \<^term>\<open>((b1::bool) \<and> b2 \<and> b3 \<and> b4 \<and> b5 \<and> b6 \<and> b7 \<and> b8 \<and> b9 \<and> b10 \<and>
           b11 \<and> b12 \<and> b13 \<and> b14 \<and> b15 \<and> b16 \<and> b17 \<and> b18 \<and> b19 \<and> b20)
          \<longrightarrow> G \<and> H\<close>
  ]
  val expected_per_prem = [3, 2, 2, 1]
in
  val _ = writeln "=== full-agent-flow regression (strip_meta_and_hol_hhf output) ==="
  val _ = app (fn (prem, expected) =>
             let val atoms = Minilang.deep_destruct_term ctxt prem
                 val n = length atoms
                 val ok = n = expected
             in writeln ((if ok then "OK  " else "FAIL ") ^
                         Syntax.string_of_term ctxt prem ^
                         "  -->  " ^ string_of_int n ^
                         " atoms (expected " ^ string_of_int expected ^ ")")
             end) (prems ~~ expected_per_prem)
end
\<close>

end
