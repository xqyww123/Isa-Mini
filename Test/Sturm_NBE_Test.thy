theory Sturm_NBE_Test
  imports Sturm_Sequences.Sturm_Method Auto_Sledgehammer.Auto_Sledgehammer
begin

text \<open>Test: replace sturm's Code_Runtime.dynamic_holds_conv with Nbe.dynamic_conv\<close>

ML \<open>
structure Sturm_NBE = struct

fun nbe_holds_conv ctxt ct =
  let
    val eq = Nbe.dynamic_conv ctxt ct
    val rhs = Thm.rhs_of eq |> Thm.term_of
  in
    if rhs aconv @{term "Trueprop True"}
       orelse rhs aconv @{prop "True"}
    then
      SOME (eq RS @{thm meta_eq_to_obj_eq} RS @{thm Eq_TrueI})
      handle THM _ => NONE
    else NONE
  end
  handle Match => NONE | THM _ => NONE | ERROR _ => NONE

fun sturm_nbe_tac ctxt =
  let
    val sturm_preprocess =
      EVERY' [
        Object_Logic.full_atomize_tac ctxt,
        EqSubst.eqsubst_tac ctxt [0] @{thms sturm_imp_conv},
        Object_Logic.full_atomize_tac ctxt,
        Sturm.sturm_tac ctxt false  (* use the full tactic but we'll time it *)
      ]
  in sturm_preprocess end

end
\<close>

text \<open>Approach 1: Just try Nbe.dynamic_conv directly on the preprocessed term.
     We need to see if NBE can evaluate sturm-related functions.\<close>

ML \<open>
(* Simple test: can NBE evaluate count_roots on a concrete polynomial? *)
val test_ct = \<^cterm>\<open>count_roots [:- 1, 0, 1 :: real:] = 2\<close>
val _ = writeln "Testing NBE on count_roots..."
val nbe_result = Timeout.apply (Time.fromSeconds 30) (fn () =>
    Nbe.dynamic_conv \<^context> (Thm.apply \<^cterm>\<open>Trueprop\<close> test_ct)
  ) ()
  handle Timeout.TIMEOUT _ => (writeln "NBE timed out!"; @{thm TrueI})
       | ERROR msg => (writeln ("NBE error: " ^ msg); @{thm TrueI})
val _ = writeln ("NBE result: " ^ \<^make_string> nbe_result)
\<close>

text \<open>Approach 2: Test Code_Simp as an alternative backend\<close>

ML \<open>
val _ = writeln "Testing Code_Simp on count_roots..."
val simp_result = Timeout.apply (Time.fromSeconds 30) (fn () =>
    Code_Simp.dynamic_conv \<^context> (Thm.apply \<^cterm>\<open>Trueprop\<close> test_ct)
  ) ()
  handle Timeout.TIMEOUT _ => (writeln "Code_Simp timed out!"; @{thm TrueI})
       | ERROR msg => (writeln ("Code_Simp error: " ^ msg); @{thm TrueI})
val _ = writeln ("Code_Simp result: " ^ \<^make_string> simp_result)
\<close>

text \<open>Approach 3: Test the existing eval_ground on the same term\<close>

ML \<open>
val _ = writeln "Testing eval_ground on count_roots..."
val eval_result = Timeout.apply (Time.fromSeconds 30) (fn () =>
    Ground_Eval.eval_ground 30 \<^context> test_ct
  ) ()
  handle Timeout.TIMEOUT _ => (writeln "eval_ground timed out!"; NONE)
       | ERROR msg => (writeln ("eval_ground error: " ^ msg); NONE)
val _ = writeln ("eval_ground result: " ^ \<^make_string> eval_result)
\<close>

text \<open>Now test the full sturm pipeline with timing\<close>

ML \<open>
fun time_sturm msg tac ctxt goal =
  let
    val start = Timing.start ()
    val result = SINGLE (tac ctxt false 1) goal
    val timing = Timing.result start
    val _ = writeln (msg ^ ": " ^ Timing.message timing)
  in result end
\<close>

text \<open>Test 1: Original sturm on x^2+1>0\<close>
ML \<open>
val goal1 = Goal.init (\<^cterm>\<open>Trueprop (\<forall>x::real. x^2 + 1 > 0)\<close>)
val _ = writeln "=== Timing original sturm ==="
val r1 = time_sturm "sturm(x^2+1>0)" Sturm.sturm_tac \<^context> goal1
val _ = writeln ("Result: " ^ (case r1 of SOME _ => "SUCCESS" | NONE => "FAIL"))
\<close>

text \<open>Test 2: Original sturm on x>1 implies x^3>1\<close>
ML \<open>
val goal2 = Goal.init (\<^cterm>\<open>Trueprop (\<forall>x::real. x > 1 \<longrightarrow> x^3 > 1)\<close>)
val _ = writeln "=== Timing original sturm ==="
val r2 = time_sturm "sturm(x>1->x^3>1)" Sturm.sturm_tac \<^context> goal2
val _ = writeln ("Result: " ^ (case r2 of SOME _ => "SUCCESS" | NONE => "FAIL"))
\<close>

text \<open>Test 3: Degree 10\<close>
ML \<open>
val goal3 = Goal.init (\<^cterm>\<open>Trueprop (\<forall>x::real. x^10 + 1 > 0)\<close>)
val _ = writeln "=== Timing original sturm ==="
val r3 = time_sturm "sturm(x^10+1>0)" Sturm.sturm_tac \<^context> goal3
val _ = writeln ("Result: " ^ (case r3 of SOME _ => "SUCCESS" | NONE => "FAIL"))
\<close>

end
