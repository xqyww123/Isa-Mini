theory Ball_InstUniv_Test
  imports Minilang.Minilang
begin

declare [[quick_and_dirty]]

text \<open>Tests for extending @{ML Minilang_Aux.inst_universal_quantifiers}
  and @{ML Minilang_Aux.xwhere} with Ball (bounded quantification) support.

  These tests document the DESIRED behavior. They will fail until the
  implementation is extended. Mark sections that currently fail with
  explicit error handling so the file processes cleanly.\<close>

ML \<open>
open Minilang_Aux

fun test_ok label ctxt insts thm =
  let val result =
    (let val thm' = inst_universal_quantifiers ctxt (insts, []) thm
     in "OK: " ^ Thm.string_of_thm ctxt thm' end)
    handle ERROR msg => "FAIL: " ^ msg
  in writeln (label ^ ": " ^ result) end

fun test_fail label ctxt insts thm =
  let val result =
    (inst_universal_quantifiers ctxt (insts, []) thm;
     "BUG: should have failed")
    handle ERROR _ => "OK: correctly rejected"
  in writeln (label ^ ": " ^ result) end

fun VN name = VN_IndexName (name, 0)
fun VNi name idx = VN_IndexName (name, idx)

val ctxt0 = \<^context>
val nat = \<^typ>\<open>nat\<close>
val nat_set = \<^typ>\<open>nat set\<close>
val P1 = Free("P", \<^typ>\<open>nat \<Rightarrow> bool\<close>)
val P2 = Free("P", \<^typ>\<open>nat \<Rightarrow> nat \<Rightarrow> bool\<close>)
val P3 = Free("P", \<^typ>\<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close>)
val A = Free("A", nat_set)
val B = Free("B", nat_set)
fun N n = HOLogic.mk_number nat n
fun mk thm = Skip_Proof.make_thm (Proof_Context.theory_of ctxt0) thm

fun raw_hol_all name T body =
  Const(\<^const_name>\<open>HOL.All\<close>, (T --> \<^typ>\<open>bool\<close>) --> \<^typ>\<open>bool\<close>) $ Abs(name, T, body)

fun raw_ball name T S body =
  Const(\<^const_name>\<open>Set.Ball\<close>, HOLogic.mk_setT T --> (T --> \<^typ>\<open>bool\<close>) --> \<^typ>\<open>bool\<close>)
    $ S $ Abs(name, T, body)
\<close>

section \<open>Verification of the new commutativity lemmas\<close>

text \<open>Verify the lemmas compile and are correct.\<close>

ML \<open>
val _ = writeln ("Ball_All_comm: " ^ Thm.string_of_thm ctxt0 @{thm Ball_All_comm})
val _ = writeln ("All_Ball_comm: " ^ Thm.string_of_thm ctxt0 @{thm All_Ball_comm})
val _ = writeln ("Ball_Ball_comm: " ^ Thm.string_of_thm ctxt0 @{thm Ball_Ball_comm})
val _ = writeln ("pull_Ball_eq: " ^ Thm.string_of_thm ctxt0 @{thm pull_Ball_eq})
\<close>

text \<open>Verify folded forms work for Conv.rewr_conv.\<close>
ML \<open>
val _ = writeln ("Ball_All_comm[folded atomize_eq]: " ^
  Thm.string_of_thm ctxt0 @{thm Ball_All_comm[folded atomize_eq]})
val _ = writeln ("All_Ball_comm[folded atomize_eq]: " ^
  Thm.string_of_thm ctxt0 @{thm All_Ball_comm[folded atomize_eq]})
val _ = writeln ("Ball_Ball_comm[folded atomize_eq]: " ^
  Thm.string_of_thm ctxt0 @{thm Ball_Ball_comm[folded atomize_eq]})
\<close>


section \<open>1. Ball instantiation — basic cases\<close>

subsection \<open>1.1 Simple Ball: \<open>\<forall>x\<in>A. P x\<close>, instantiate x\<close>

text \<open>After instantiating x := 5, expect: \<open>5 \<in> A \<Longrightarrow> P 5\<close>
  (membership becomes a premise via bspec).\<close>
ML \<open>
let
  val thm = mk (HOLogic.mk_Trueprop (raw_ball "x" nat A (P1 $ Bound 0)))
  val _ = writeln ("1.1 input: " ^ Thm.string_of_thm ctxt0 thm)
in
  test_ok "1.1: Ball simple inst x" ctxt0
    [(VN "x", N 5)] thm
end
\<close>

subsection \<open>1.2 Ball with two variables: \<open>\<forall>x\<in>A. \<forall>y\<in>B. P x y\<close>, instantiate both\<close>

ML \<open>
let
  val thm = mk (HOLogic.mk_Trueprop
    (raw_ball "x" nat A (raw_ball "y" nat B (P2 $ Bound 1 $ Bound 0))))
  val _ = writeln ("1.2 input: " ^ Thm.string_of_thm ctxt0 thm)
in
  test_ok "1.2: Ball-Ball inst both" ctxt0
    [(VN "x", N 1), (VN "y", N 2)] thm
end
\<close>

subsection \<open>1.3 Ball partial: \<open>\<forall>x\<in>A. \<forall>y\<in>B. P x y\<close>, instantiate x only\<close>

ML \<open>
let
  val thm = mk (HOLogic.mk_Trueprop
    (raw_ball "x" nat A (raw_ball "y" nat B (P2 $ Bound 1 $ Bound 0))))
  val _ = writeln ("1.3 input: " ^ Thm.string_of_thm ctxt0 thm)
in
  test_ok "1.3: Ball-Ball partial (x only)" ctxt0
    [(VN "x", N 1)] thm
end
\<close>

subsection \<open>1.4 Ball inner only: \<open>\<forall>x\<in>A. \<forall>y\<in>B. P x y\<close>, instantiate y only (requires reorder)\<close>

ML \<open>
let
  val thm = mk (HOLogic.mk_Trueprop
    (raw_ball "x" nat A (raw_ball "y" nat B (P2 $ Bound 1 $ Bound 0))))
  val _ = writeln ("1.4 input: " ^ Thm.string_of_thm ctxt0 thm)
in
  test_ok "1.4: Ball-Ball inner (y only, needs swap)" ctxt0
    [(VN "y", N 2)] thm
end
\<close>


section \<open>2. Mixed All and Ball\<close>

subsection \<open>2.1 All then Ball: \<open>\<forall>x. \<forall>y\<in>B. P x y\<close>\<close>

ML \<open>
let
  val thm = mk (HOLogic.mk_Trueprop
    (raw_hol_all "x" nat (raw_ball "y" nat B (P2 $ Bound 1 $ Bound 0))))
  val _ = writeln ("2.1 input: " ^ Thm.string_of_thm ctxt0 thm)
in
  test_ok "2.1a: All-Ball inst both" ctxt0
    [(VN "x", N 1), (VN "y", N 2)] thm;
  test_ok "2.1b: All-Ball inst x only" ctxt0
    [(VN "x", N 1)] thm;
  test_ok "2.1c: All-Ball inst y only (needs swap)" ctxt0
    [(VN "y", N 2)] thm
end
\<close>

subsection \<open>2.2 Ball then All: \<open>\<forall>x\<in>A. \<forall>y. P x y\<close>\<close>

ML \<open>
let
  val thm = mk (HOLogic.mk_Trueprop
    (raw_ball "x" nat A (raw_hol_all "y" nat (P2 $ Bound 1 $ Bound 0))))
  val _ = writeln ("2.2 input: " ^ Thm.string_of_thm ctxt0 thm)
in
  test_ok "2.2a: Ball-All inst both" ctxt0
    [(VN "x", N 1), (VN "y", N 2)] thm;
  test_ok "2.2b: Ball-All inst x only" ctxt0
    [(VN "x", N 1)] thm;
  test_ok "2.2c: Ball-All inst y only (needs swap)" ctxt0
    [(VN "y", N 2)] thm
end
\<close>

subsection \<open>2.3 Three-way mix: \<open>\<forall>x. \<forall>y\<in>A. \<forall>z. P x y z\<close>\<close>

ML \<open>
let
  val thm = mk (HOLogic.mk_Trueprop
    (raw_hol_all "x" nat
      (raw_ball "y" nat A
        (raw_hol_all "z" nat
          (P3 $ Bound 2 $ Bound 1 $ Bound 0)))))
  val _ = writeln ("2.3 input: " ^ Thm.string_of_thm ctxt0 thm)
in
  test_ok "2.3a: All-Ball-All inst all" ctxt0
    [(VN "x", N 1), (VN "y", N 2), (VN "z", N 3)] thm;
  test_ok "2.3b: inst y only" ctxt0
    [(VN "y", N 2)] thm;
  test_ok "2.3c: inst z only (needs swap past Ball)" ctxt0
    [(VN "z", N 3)] thm;
  test_ok "2.3d: inst x and z (skip Ball y)" ctxt0
    [(VN "x", N 1), (VN "z", N 3)] thm
end
\<close>


section \<open>3. Ball behind HOL implication\<close>

subsection \<open>3.1 \<open>\<forall>x. P x \<longrightarrow> (\<forall>y\<in>A. Q x y)\<close>\<close>

text \<open>Ball nested inside HOL implies — pull_ball must pull Ball through \<open>\<longrightarrow>\<close>.\<close>
ML \<open>
let
  val Q = Free("Q", \<^typ>\<open>nat \<Rightarrow> nat \<Rightarrow> bool\<close>)
  val thm = mk (HOLogic.mk_Trueprop
    (raw_hol_all "x" nat
      (HOLogic.mk_imp (P1 $ Bound 0,
        raw_ball "y" nat A (Q $ Bound 1 $ Bound 0)))))
  val _ = writeln ("3.1 input: " ^ Thm.string_of_thm ctxt0 thm)
in
  test_ok "3.1a: inst both" ctxt0
    [(VN "x", N 1), (VN "y", N 2)] thm;
  test_ok "3.1b: inst y only" ctxt0
    [(VN "y", N 2)] thm
end
\<close>


section \<open>4. Ball with Pure quantifiers and schematics\<close>

subsection \<open>4.1 Pure.all + Ball: \<open>\<And>n. \<forall>x\<in>A. P n x\<close>\<close>

ML \<open>
let
  val thm = mk (
    Logic.all_const nat $ Abs("n", nat,
      HOLogic.mk_Trueprop (raw_ball "x" nat A (P2 $ Bound 1 $ Bound 0))))
  val _ = writeln ("4.1 input: " ^ Thm.string_of_thm ctxt0 thm)
in
  test_ok "4.1a: inst n (Pure) and x (Ball)" ctxt0
    [(VN "n", N 5), (VN "x", N 10)] thm;
  test_ok "4.1b: inst x (Ball) only" ctxt0
    [(VN "x", N 10)] thm;
  test_ok "4.1c: inst n (Pure) only" ctxt0
    [(VN "n", N 5)] thm
end
\<close>

subsection \<open>4.2 Schematic + Ball: \<open>\<forall>x\<in>A. P ?n x\<close>\<close>

ML \<open>
let
  val thm = mk (HOLogic.mk_Trueprop
    (raw_ball "x" nat A (P2 $ Var(("n",0), nat) $ Bound 0)))
  val _ = writeln ("4.2 input: " ^ Thm.string_of_thm ctxt0 thm)
in
  test_ok "4.2a: inst n (schematic) and x (Ball)" ctxt0
    [(VN "n", N 5), (VN "x", N 10)] thm;
  test_ok "4.2b: inst x (Ball) only" ctxt0
    [(VN "x", N 10)] thm;
  test_ok "4.2c: inst n (schematic) only" ctxt0
    [(VN "n", N 5)] thm
end
\<close>

subsection \<open>4.3 All three: Pure + schematic + Ball\<close>

ML \<open>
let
  val thm = mk (
    Logic.all_const nat $ Abs("a", nat,
      HOLogic.mk_Trueprop
        (raw_ball "x" nat A (P3 $ Bound 1 $ Var(("c",0), nat) $ Bound 0))))
  val _ = writeln ("4.3 input: " ^ Thm.string_of_thm ctxt0 thm)
in
  test_ok "4.3: Pure a + schematic c + Ball x" ctxt0
    [(VN "a", N 1), (VN "c", N 2), (VN "x", N 3)] thm
end
\<close>


section \<open>5. Ball behind Pure.imp (premise position)\<close>

subsection \<open>5.1 \<open>Q \<Longrightarrow> \<forall>x\<in>A. P x\<close> — Ball in conclusion behind Pure.imp\<close>

ML \<open>
let
  val Q = Free("Q", \<^typ>\<open>bool\<close>)
  val thm = mk (
    Logic.mk_implies (HOLogic.mk_Trueprop Q,
      HOLogic.mk_Trueprop (raw_ball "x" nat A (P1 $ Bound 0))))
  val _ = writeln ("5.1 input: " ^ Thm.string_of_thm ctxt0 thm)
in
  test_ok "5.1: Ball behind Pure.imp" ctxt0
    [(VN "x", N 5)] thm
end
\<close>


section \<open>6. xwhere with Ball\<close>

subsection \<open>6.1 xwhere attribute on Ball fact\<close>

lemma ball_test_fact: \<open>\<forall>x\<in>A. \<forall>y\<in>B. P x y\<close> for A B :: \<open>nat set\<close> and P :: \<open>nat \<Rightarrow> nat \<Rightarrow> bool\<close>
  sorry

ML \<open>
let val ctxt = \<^context>
    val thm = @{thm ball_test_fact}
    val _ = writeln ("6.1 input: " ^ Thm.string_of_thm ctxt thm)
in
  (let val result = Minilang_Aux.inst_universal_quantifiers' ctxt
        [(VN "x", "0::nat"), (VN "y", "1::nat")] thm
   in writeln ("6.1 xwhere both: OK: " ^ Thm.string_of_thm ctxt result) end
   handle ERROR msg => writeln ("6.1 xwhere both: FAIL: " ^ msg))
end
\<close>

subsection \<open>6.2 xwhere attribute on mixed All+Ball fact\<close>

lemma mixed_test_fact: \<open>\<forall>x. \<forall>y\<in>A. P x y\<close> for A :: \<open>nat set\<close> and P :: \<open>nat \<Rightarrow> nat \<Rightarrow> bool\<close>
  sorry

ML \<open>
let val ctxt = \<^context>
    val thm = @{thm mixed_test_fact}
    val _ = writeln ("6.2 input: " ^ Thm.string_of_thm ctxt thm)
in
  (let val result = Minilang_Aux.inst_universal_quantifiers' ctxt
        [(VN "x", "0::nat"), (VN "y", "1::nat")] thm
   in writeln ("6.2 xwhere All+Ball: OK: " ^ Thm.string_of_thm ctxt result) end
   handle ERROR msg => writeln ("6.2 xwhere All+Ball: FAIL: " ^ msg))
end
\<close>


section \<open>7. SPECIALIZE (Derive) with Ball\<close>

subsection \<open>7.1 SPECIALIZE on Ball rule via min_script\<close>

lemma ball_spec_rule: \<open>\<forall>x\<in>A. P x\<close> for A :: \<open>nat set\<close> and P :: \<open>nat \<Rightarrow> bool\<close>
  sorry

text \<open>This test uses min_script SPECIALIZE with a Ball-quantified rule.
  Expected: instantiate x, membership premise \<open>t \<in> A\<close> appears.\<close>
ML \<open>
let val ctxt = \<^context>
    val thm = @{thm ball_spec_rule}
    val _ = writeln ("7.1 input: " ^ Thm.string_of_thm ctxt thm)
    val result = Minilang_Aux.inst_universal_quantifiers' ctxt
      [(VN "x", "0::nat")] thm
    val _ = writeln ("7.1 SPECIALIZE Ball: OK: " ^ Thm.string_of_thm ctxt result)
in () end
handle ERROR msg => writeln ("7.1 SPECIALIZE Ball: FAIL: " ^ msg)
\<close>

subsection \<open>7.2 SPECIALIZE on Ball rule with discharge\<close>

text \<open>After instantiation, the membership premise should be dischargeable.\<close>
ML \<open>
let val ctxt = \<^context>
    val thm = @{thm ball_spec_rule}
    val membership = Skip_Proof.make_thm (Proof_Context.theory_of ctxt)
      (HOLogic.mk_Trueprop (HOLogic.mk_mem (N 0, Free("A", nat_set))))
    val result = Minilang_Aux.inst_universal_quantifiers' ctxt
      [(VN "x", "0::nat")] thm
    val _ = writeln ("7.2 after inst: " ^ Thm.string_of_thm ctxt result)
    val discharged = Minilang_Aux.xOF false ctxt [SOME membership] result
    val _ = writeln ("7.2 after discharge: OK: " ^ Thm.string_of_thm ctxt discharged)
in () end
handle ERROR msg => writeln ("7.2 SPECIALIZE+discharge: FAIL: " ^ msg)
     | THM (msg,_,_) => writeln ("7.2 SPECIALIZE+discharge: FAIL(THM): " ^ msg)
\<close>


section \<open>8. Edge cases\<close>

subsection \<open>8.1 Ball variable not found\<close>

ML \<open>
let
  val thm = mk (HOLogic.mk_Trueprop (raw_ball "x" nat A (P1 $ Bound 0)))
in
  test_fail "8.1: nonexistent var in Ball" ctxt0
    [(VN "z", N 5)] thm
end
\<close>

subsection \<open>8.2 Empty instantiation on Ball — identity\<close>

ML \<open>
let
  val thm = mk (HOLogic.mk_Trueprop (raw_ball "x" nat A (P1 $ Bound 0)))
in
  test_ok "8.2: empty inst on Ball" ctxt0 [] thm
end
\<close>

subsection \<open>8.3 Ball with HOL implication body: \<open>\<forall>x\<in>A. P x \<longrightarrow> Q x\<close>\<close>

ML \<open>
let
  val Q1 = Free("Q", \<^typ>\<open>nat \<Rightarrow> bool\<close>)
  val thm = mk (HOLogic.mk_Trueprop
    (raw_ball "x" nat A (HOLogic.mk_imp (P1 $ Bound 0, Q1 $ Bound 0))))
  val _ = writeln ("8.3 input: " ^ Thm.string_of_thm ctxt0 thm)
in
  test_ok "8.3: Ball with body implication" ctxt0
    [(VN "x", N 5)] thm
end
\<close>

subsection \<open>8.4 Deep nesting: \<open>\<forall>a\<in>A. \<forall>b. c \<longrightarrow> \<forall>d\<in>B. P a b d\<close>\<close>

ML \<open>
let
  val c_prop = Free("c", \<^typ>\<open>bool\<close>)
  val thm = mk (HOLogic.mk_Trueprop
    (raw_ball "a" nat A
      (raw_hol_all "b" nat
        (HOLogic.mk_imp (c_prop,
          raw_ball "d" nat B
            (P3 $ Bound 2 $ Bound 1 $ Bound 0))))))
  val _ = writeln ("8.4 input: " ^ Thm.string_of_thm ctxt0 thm)
in
  test_ok "8.4a: inst all three" ctxt0
    [(VN "a", N 1), (VN "b", N 2), (VN "d", N 3)] thm;
  test_ok "8.4b: inst d only (deep Ball behind implication)" ctxt0
    [(VN "d", N 3)] thm;
  test_ok "8.4c: inst a and d (skip All b)" ctxt0
    [(VN "a", N 1), (VN "d", N 3)] thm
end
\<close>


section \<open>9. Interaction with existing All-only tests (regression)\<close>

text \<open>Ensure existing All-only behavior is unchanged.\<close>

subsection \<open>9.1 Plain All still works\<close>

ML \<open>
let
  val ctxt = \<^context>
  val thm = @{lemma \<open>\<forall>x y :: nat. x < y \<longrightarrow> x \<le> y\<close> by auto}
in
  test_ok "9.1a: All full" ctxt
    [(VN "x", N 0), (VN "y", N 1)] thm;
  test_ok "9.1b: All partial" ctxt
    [(VN "x", N 0)] thm;
  test_ok "9.1c: All inner only (reorder)" ctxt
    [(VN "y", N 1)] thm
end
\<close>

subsection \<open>9.2 Pure.all still works\<close>

ML \<open>
let
  val ctxt = \<^context>
  val thm = @{thm conjI}
in
  test_ok "9.2: Pure.all" ctxt
    [(VN "P", \<^term>\<open>True\<close>), (VN "Q", \<^term>\<open>False\<close>)] thm
end
\<close>

subsection \<open>9.3 Schematic still works\<close>

ML \<open>
let
  val ctxt = \<^context>
  val thm = @{thm mp}
in
  test_ok "9.3: schematic" ctxt
    [(VN "P", \<^term>\<open>True\<close>), (VN "Q", \<^term>\<open>False\<close>)] thm
end
\<close>


end
