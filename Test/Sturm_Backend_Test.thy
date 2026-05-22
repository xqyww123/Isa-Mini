theory Sturm_Backend_Test
  imports Sturm_Sequences.Sturm_Method Auto_Sledgehammer.Auto_Sledgehammer
begin

text \<open>Compare backends on the FULL sturm pipeline.
  The sturm pipeline has two phases:
  1. Preprocessing: reify polynomial expressions to poly p x form (fast)
  2. Ground evaluation: evaluate the resulting boolean via code compilation (slow)

  We isolate phase 2 by manually constructing the ground boolean terms
  that sturm's preprocessing produces, then timing each backend on those.\<close>

ML \<open>
fun time_conv name conv ctxt ct =
  let
    val start = Timing.start ()
    val result = (SOME (conv ctxt ct) handle ERROR msg => (writeln (name ^ " ERROR: " ^ msg); NONE)
                                           | Match => (writeln (name ^ " Match error"); NONE))
    val timing = Timing.result start
    val _ = writeln (name ^ ": " ^ Timing.message timing ^
                     " => " ^ (case result of SOME _ => "OK" | NONE => "FAIL"))
  in result end

fun time_holds_conv name ctxt ct =
  let
    val start = Timing.start ()
    val prop_ct = Thm.apply \<^cterm>\<open>Trueprop\<close> ct
    val result = (SOME (Code_Runtime.dynamic_holds_conv ctxt prop_ct)
                  handle ERROR msg => (writeln (name ^ " ERROR: " ^ msg); NONE))
    val timing = Timing.result start
    val _ = writeln (name ^ ": " ^ Timing.message timing ^
                     " => " ^ (case result of SOME _ => "OK" | NONE => "FAIL"))
  in result end
\<close>

section \<open>Test 1: Simple ground boolean (count_roots)\<close>

ML \<open>
val ct1 = \<^cterm>\<open>count_roots [:- 1, 0, 1 :: real:] = 2\<close>
val _ = writeln "=== Test 1: count_roots [:−1,0,1:] = 2 ==="
val _ = time_conv "NBE" Nbe.dynamic_conv \<^context> (Thm.apply \<^cterm>\<open>Trueprop\<close> ct1)
val _ = time_holds_conv "dynamic_holds" \<^context> ct1
val _ = time_conv "Code_Simp" Code_Simp.dynamic_conv \<^context> (Thm.apply \<^cterm>\<open>Trueprop\<close> ct1)
\<close>

section \<open>Test 2: More complex ground boolean (poly_pos style)\<close>

text \<open>This is the kind of term sturm produces after preprocessing for
  "forall x::real. x^2 + 1 > 0":
  The preprocessed form is roughly:
    [:1, 0, 1:] \<noteq> 0 \<and> poly_inf [:1, 0, 1:] = 1 \<and> count_roots [:1, 0, 1:] = 0
  Let's test that.\<close>

ML \<open>
val ct2 = \<^cterm>\<open>[:1, 0, 1 :: real:] \<noteq> 0 \<and> 0 < poly_inf [:1, 0, 1 :: real:] \<and> count_roots [:1, 0, 1 :: real:] = 0\<close>
val _ = writeln "=== Test 2: compound sturm boolean ==="
val _ = time_conv "NBE" Nbe.dynamic_conv \<^context> (Thm.apply \<^cterm>\<open>Trueprop\<close> ct2)
val _ = time_holds_conv "dynamic_holds" \<^context> ct2
val _ = time_conv "Code_Simp" Code_Simp.dynamic_conv \<^context> (Thm.apply \<^cterm>\<open>Trueprop\<close> ct2)
\<close>

section \<open>Test 3: Higher degree polynomial\<close>

ML \<open>
val ct3 = \<^cterm>\<open>[:1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 :: real:] \<noteq> 0
  \<and> 0 < poly_inf [:1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 :: real:]
  \<and> count_roots [:1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1 :: real:] = 0\<close>
val _ = writeln "=== Test 3: degree-10 polynomial boolean ==="
val _ = time_conv "NBE" Nbe.dynamic_conv \<^context> (Thm.apply \<^cterm>\<open>Trueprop\<close> ct3)
val _ = time_holds_conv "dynamic_holds" \<^context> ct3
val _ = time_conv "Code_Simp" Code_Simp.dynamic_conv \<^context> (Thm.apply \<^cterm>\<open>Trueprop\<close> ct3)
\<close>

section \<open>Test 4: NBE cold vs warm (run NBE twice to see caching effect)\<close>

ML \<open>
val _ = writeln "=== Test 4: NBE cold vs warm ==="
val ct4 = \<^cterm>\<open>count_roots [:1, -3, 3, -1 :: real:] = 1\<close>
val _ = time_conv "NBE-call1" Nbe.dynamic_conv \<^context> (Thm.apply \<^cterm>\<open>Trueprop\<close> ct4)
val _ = time_conv "NBE-call2" Nbe.dynamic_conv \<^context> (Thm.apply \<^cterm>\<open>Trueprop\<close> ct4)

val ct5 = \<^cterm>\<open>count_roots [:6, -11, 6, -1 :: real:] = 3\<close>
val _ = time_conv "NBE-new-poly" Nbe.dynamic_conv \<^context> (Thm.apply \<^cterm>\<open>Trueprop\<close> ct5)
\<close>

section \<open>Test 5: Full sturm tactic vs NBE-based variant\<close>

text \<open>Build a variant of sturm that uses NBE instead of dynamic_holds_conv
  for the final evaluation step. We can't easily swap the conv inside
  sturm.ML, but we can rebuild the pipeline.\<close>

ML \<open>
(* A variant that does: sturm preprocessing + NBE evaluation *)
fun sturm_nbe_tac ctxt i st =
  let
    (* Phase 1: Run sturm preprocessing only (up to but not including sturm_conv).
       Since we can't split sturm_tac internally, we instead:
       Run the full sturm_tac but with a modified context...
       Actually, let's just test: run full sturm and see if code_reflect helps. *)
    val _ = ()
  in Seq.empty end

(* For now, let's test code_reflect approach instead *)
val _ = writeln "=== code_reflect not yet tested (need to add to .thy) ==="
\<close>

end
