theory Test_SplitConjs2_Scratch
  imports Minilang.Minilang
begin

section \<open>Part A: ML-level goal-count tests\<close>

ML \<open>
local
  val ctxt0 = \<^context>
  fun L s = tracing s
  val _ = Minilang.set_reporter (K ())

  fun mk_state s =
    Syntax.read_prop ctxt0 s
    |> Thm.cterm_of ctxt0
    |> Goal.init
    |> Minilang.INIT ctxt0

  (* Run SPLIT_CONJS2 and assert the resulting number of goals. *)
  fun chk2 name s expected =
    let val st = Minilang.SPLIT_CONJS2 (mk_state s)
        val n = Minilang.num_goals st
        val _ = L (name ^ " : " ^ s ^ "  ==>  " ^ Int.toString n
                   ^ " goals (expected " ^ Int.toString expected ^ ")")
     in \<^assert> (n = expected) end

  (* Assert SPLIT_CONJS2 rejects a non-conjunction (even after distribution). *)
  fun chk_reject name s =
    (\<^try>\<open>
       let val _ = Minilang.SPLIT_CONJS2 (mk_state s)
        in error (name ^ ": expected OPR_FAIL but none raised") end
       catch Minilang.OPR_FAIL (Minilang.INVALID_OPR, _) =>
         L (name ^ " : " ^ s ^ "  ==>  correctly rejected") \<close>)

  (* Cross-check: where SPLIT_CONJS already works, SPLIT_CONJS2 agrees. *)
  fun chk_agree name s =
    let val n1 = Minilang.num_goals (Minilang.SPLIT_CONJS  (mk_state s))
        val n2 = Minilang.num_goals (Minilang.SPLIT_CONJS2 (mk_state s))
        val _ = L (name ^ " : " ^ s ^ "  SPLIT_CONJS=" ^ Int.toString n1
                   ^ " SPLIT_CONJS2=" ^ Int.toString n2)
     in \<^assert> (n1 = n2) end
in
  (* --- plain RIGHT-nested conjunctions: identical to SPLIT_CONJS --- *)
  val _ = chk_agree "A1" "P \<and> Q"
  val _ = chk_agree "A2" "P \<and> Q \<and> R"
  val _ = chk_agree "A3" "P \<and> Q \<and> R \<and> S \<and> T"
  (* A4: left-nested.  Plain SPLIT_CONJS splits only the right spine (3 goals);
     SPLIT_CONJS2 re-associates first, so it fully splits into 4. *)
  val _ = chk2 "A4" "(P \<and> Q) \<and> (R \<and> S)" 4

  (* --- object \<forall> distributes over \<and> --- *)
  val _ = chk2 "B1" "\<forall>x::nat. P x \<and> Q x" 2
  val _ = chk2 "B2" "\<forall>x::nat. P x \<and> Q x \<and> R x" 3
  val _ = chk2 "B3" "\<forall>x y::nat. P x y \<and> Q x y" 2   (* two leading \<forall> *)

  (* --- object \<longrightarrow> distributes over \<and> --- *)
  val _ = chk2 "C1" "P \<longrightarrow> (A \<and> B)" 2
  val _ = chk2 "C2" "P \<longrightarrow> Q \<longrightarrow> (A \<and> B \<and> C)" 3
  val _ = chk2 "C3" "\<forall>x::nat. P x \<longrightarrow> (A x \<and> B x)" 2

  (* --- bounded quantifier \<forall>x\<in>S (the *Ball* constant): distributes via
         ball_conj_distrib --- *)
  val _ = chk2 "D1" "\<forall>x\<in>S. A x \<and> B x" 2
  val _ = chk2 "D2" "\<forall>x\<in>S. A x \<and> B x \<and> C x" 3

  (* --- deep nesting: one SPLIT_CONJS2 flattens the whole nest --- *)
  val _ = chk2 "E1" "\<forall>x::nat. A x \<and> (\<forall>y::nat. B x y \<and> C x y)" 3
  val _ = chk2 "E2"
      "\<forall>x::nat. A x \<and> (\<forall>y::nat. B x y \<and> (\<forall>z::nat. C x y z \<and> D x y z))" 4
  (* E3: distribution yields a LEFT-nested conj ((\<forall>\<forall>P)\<and>(\<forall>\<forall>Q))\<and>(\<forall>R); the
     conj_assoc pass re-associates it, so it now fully splits into 3. *)
  val _ = chk2 "E3"
      "\<forall>x::nat. (\<forall>y::nat. P x y \<and> Q x y) \<and> R x" 3
  (* E4: bounded + nested + left-association together *)
  val _ = chk2 "E4"
      "\<forall>x\<in>S. (\<forall>y\<in>T. P x y \<and> Q x y) \<and> R x" 3

  (* --- mixed \<longrightarrow>/\<forall>/\<longrightarrow>/\<and> (the reviewer's case): A \<longrightarrow> B \<longrightarrow> \<forall>x. (C \<longrightarrow> D \<and> E) --- *)
  val _ = chk2 "H1" "A \<longrightarrow> B \<longrightarrow> (\<forall>x::nat. C x \<longrightarrow> (D x \<and> E x))" 2
  val _ = chk2 "H2"
      "A \<longrightarrow> B \<longrightarrow> (\<forall>x::nat. C x \<longrightarrow> (D x \<and> E x \<and> (\<forall>y::nat. F x y \<and> G x y)))" 4

  (* --- \<exists> must NOT be distributed (no \<exists>-distrib); the top \<and> still splits --- *)
  val _ = chk2 "F1" "\<forall>x::nat. (\<exists>y::nat. P x y) \<and> Q x" 2
  (* an \<exists> wrapping a conj is left intact -> still a top-level conj? no: head is \<exists> *)
  val _ = chk_reject "F2" "\<exists>y::nat. P y \<and> Q y"

  (* --- negative cases: nothing to split --- *)
  val _ = chk_reject "G1" "P (b::bool)"
  val _ = chk_reject "G2" "\<forall>x::nat. P x"
  val _ = chk_reject "G3" "\<forall>x::nat. P x \<longrightarrow> Q x"           (* consequent not a conj *)
  val _ = chk_reject "G4" "(A \<and> B) \<longrightarrow> C"                  (* conj only in antecedent *)

  val _ = L "=== Part A (counts) completed ==="
end
\<close>

section \<open>Part B: end-to-end soundness+completeness via min_script\<close>

text \<open>If these evaluate without error, SPLIT_CONJS2 produced a sound and
      complete decomposition (the kernel reconstructs the original goal).\<close>

text \<open>nested \<forall>/\<and>, three leaves\<close>
lemma "\<forall>x::nat. x = x \<and> (\<forall>y::nat. y + 0 = y \<and> x + y = y + x)"
  apply (min_script \<open>
  SPLIT_CONJS2
  SIMP
  NEXT
  SIMP
  NEXT
  SIMP
  END
\<close>)
  done

text \<open>\<longrightarrow> over \<and> under \<forall>\<close>
lemma "\<forall>x::nat. x > 0 \<longrightarrow> (x \<ge> 1 \<and> x + x > x)"
  apply (min_script \<open>
  SPLIT_CONJS2
  SIMP
  NEXT
  SIMP
  END
\<close>)
  done

text \<open>the reviewer's mixed pattern: A \<longrightarrow> B \<longrightarrow> \<forall>x. (C \<longrightarrow> D \<and> E), concrete and provable\<close>
lemma "(0::nat) < 1 \<longrightarrow> (1::nat) < 2 \<longrightarrow>
        (\<forall>x::nat. x > 0 \<longrightarrow> (x \<ge> 1 \<and> x + x \<ge> x))"
  apply (min_script \<open>
  SPLIT_CONJS2
  SIMP
  NEXT
  SIMP
  END
\<close>)
  done

text \<open>bounded quantifier over a conjunction (Ball), end to end\<close>
lemma "\<forall>x\<in>{1::nat..10}. x \<ge> 1 \<and> x \<le> 10"
  apply (min_script \<open>
  SPLIT_CONJS2
  SIMP
  NEXT
  SIMP
  END
\<close>)
  done

text \<open>left-nested conjunction fully splits in one step (conj_assoc pass)\<close>
lemma "((1::nat) = 1 \<and> (2::nat) = 2) \<and> ((3::nat) = 3 \<and> (4::nat) = 4)"
  apply (min_script \<open>
  SPLIT_CONJS2
  SIMP
  NEXT
  SIMP
  NEXT
  SIMP
  NEXT
  SIMP
  END
\<close>)
  done

text \<open>plain conjunction still works exactly like SPLIT_CONJS\<close>
lemma "True \<and> True \<and> True"
  apply (min_script \<open>
  SPLIT_CONJS2
  SIMP
  NEXT
  SIMP
  NEXT
  SIMP
  END
\<close>)
  done

end
