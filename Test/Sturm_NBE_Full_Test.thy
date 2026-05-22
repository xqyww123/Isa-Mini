theory Sturm_NBE_Full_Test
  imports Sturm_Sequences.Sturm_Method Auto_Sledgehammer.Auto_Sledgehammer
begin

text \<open>We can't easily swap the conv inside sturm.ML since it's sealed.
  Instead, test two approaches:
  1. Use sturm preprocessing (which is fast) + NBE for final evaluation
  2. Time the original sturm for comparison\<close>

ML \<open>
fun time_it name f =
  let
    val start = Timing.start ()
    val result = (SOME (f ()) handle ERROR msg => (writeln (name ^ " ERROR: " ^ msg); NONE)
                                   | Match => (writeln (name ^ " Match"); NONE)
                                   | Fail msg => (writeln (name ^ " Fail: " ^ msg); NONE))
    val timing = Timing.result start
    val _ = writeln (name ^ ": " ^ Timing.message timing ^
                     " => " ^ (case result of SOME _ => "OK" | NONE => "FAIL"))
  in result end

fun time_tac name tac st =
  let
    val start = Timing.start ()
    val result = SINGLE tac st
    val timing = Timing.result start
    val _ = writeln (name ^ ": " ^ Timing.message timing ^
                     " => " ^ (case result of SOME _ => "OK" | NONE => "FAIL"))
  in result end
\<close>

section \<open>Warmup NBE cache\<close>

ML \<open>
val _ = writeln "=== Warming up NBE ==="
val _ = time_it "nbe_warmup" (fn () =>
  Nbe.dynamic_conv \<^context> (Thm.apply \<^cterm>\<open>Trueprop\<close>
    \<^cterm>\<open>count_roots [:1, 0, 1 :: real:] = 0\<close>))
val _ = writeln "NBE warm"
\<close>

section \<open>Original sturm timing (for comparison)\<close>

ML \<open>
val _ = writeln "=== Original sturm ==="
val g1 = Goal.init \<^cterm>\<open>Trueprop (\<forall>x::real. x^2 + 1 > 0)\<close>
val g2 = Goal.init \<^cterm>\<open>Trueprop (\<forall>x::real. x > 1 \<longrightarrow> x^3 > 1)\<close>
val g3 = Goal.init \<^cterm>\<open>Trueprop (\<forall>x::real. x^10 + 1 > 0)\<close>
val g4 = Goal.init \<^cterm>\<open>Trueprop (\<forall>x::real. x^2 + 1 \<noteq> 0)\<close>

val _ = time_tac "orig(x^2+1>0)" (Sturm.sturm_tac \<^context> false 1) g1
val _ = time_tac "orig(x>1->x^3>1)" (Sturm.sturm_tac \<^context> false 1) g2
val _ = time_tac "orig(x^10+1>0)" (Sturm.sturm_tac \<^context> false 1) g3
val _ = time_tac "orig(x^2+1!=0)" (Sturm.sturm_tac \<^context> false 1) g4
\<close>

section \<open>Hybrid approach: sturm preprocessing then NBE evaluation\<close>

text \<open>Strategy: use sturm_tac's preprocessing steps (which are fast) to reduce
  the goal to a ground boolean, then use NBE (which is fast after warmup) to evaluate.

  Since Sturm.sturm_tac is sealed, we can't split it. But we CAN:
  1. Run the preprocessing steps (atomize, imp_conv, meta_spec, PR_TAG reification)
  2. Then run the sturm_prop_substs resolution
  3. Then evaluate with NBE instead of dynamic_holds_conv

  The preprocessing steps are accessible via the @{thms ...} antiquotations.\<close>

ML \<open>
(* NBE-based evaluation: convert goal to Trueprop True via NBE *)
fun nbe_eval_tac ctxt i st =
  (CONVERSION (Nbe.dynamic_conv ctxt) i
   THEN resolve_tac ctxt @{thms TrueI} i) st
  handle THM _ => Seq.empty | ERROR _ => Seq.empty

(* Sturm preprocessing: copied from sturm.ML lines 172-179 *)
fun sturm_preprocess_tac ctxt i =
  EVERY [
    Raw_Simplifier.prune_params_tac ctxt,
    Object_Logic.full_atomize_tac ctxt i,
    (EqSubst.eqsubst_tac ctxt [0] @{thms sturm_imp_conv} i ORELSE all_tac),
    Object_Logic.full_atomize_tac ctxt i,
    (* convert single free variable to universal quantifier *)
    (resolve_tac ctxt @{thms sturm_meta_spec} i ORELSE all_tac),
    Object_Logic.full_atomize_tac ctxt i,
    (* PR_TAG reification *)
    REPEAT_DETERM (FIRST [
      EqSubst.eqsubst_tac ctxt [0] @{thms sturm_id_PR_prio2} i,
      EqSubst.eqsubst_tac ctxt [0] @{thms sturm_id_PR_prio1} i,
      EqSubst.eqsubst_tac ctxt [0] @{thms sturm_id_PR_prio0} i]),
    simp_tac (put_simpset HOL_basic_ss ctxt addsimps
      @{thms nnf_simps not_less not_le}) i,
    REPEAT_DETERM (FIRST [
      EqSubst.eqsubst_tac ctxt [0] @{thms PR_TAG_intro_prio2} i,
      EqSubst.eqsubst_tac ctxt [0] @{thms PR_TAG_intro_prio1} i,
      EqSubst.eqsubst_tac ctxt [0] @{thms PR_TAG_intro_prio0} i])
  ]

(* Sturm prop resolution: find matching subst lemma *)
fun sturm_prop_resolve_tac ctxt i st =
  let
    fun try_thm thm = resolve_tac ctxt [thm] i st
    fun try_thms [] = Seq.empty
      | try_thms (thm :: rest) =
          case Seq.pull (try_thm thm) of
            SOME (st', _) => Seq.single st'
          | NONE => try_thms rest
  in try_thms @{thms sturm_prop_substs} end

(* Full NBE-based sturm: preprocess + resolve + NBE eval *)
fun sturm_nbe_tac ctxt i st =
  (sturm_preprocess_tac ctxt i
   THEN sturm_prop_resolve_tac ctxt i
   THEN ALLGOALS (nbe_eval_tac ctxt)) st
\<close>

ML \<open>
val _ = writeln "=== NBE-based sturm ==="
val _ = time_tac "nbe(x^2+1>0)" (sturm_nbe_tac \<^context> 1) g1
val _ = time_tac "nbe(x>1->x^3>1)" (sturm_nbe_tac \<^context> 1) g2
val _ = time_tac "nbe(x^10+1>0)" (sturm_nbe_tac \<^context> 1) g3
val _ = time_tac "nbe(x^2+1!=0)" (sturm_nbe_tac \<^context> 1) g4
\<close>

section \<open>Multiple warm NBE calls\<close>

ML \<open>
val _ = writeln "=== Warm NBE calls ==="
val g5 = Goal.init \<^cterm>\<open>Trueprop (\<forall>x::real. x^4 + 1 > 0)\<close>
val g6 = Goal.init \<^cterm>\<open>Trueprop (\<forall>x::real. x^6 + x^2 + 1 > 0)\<close>
val g7 = Goal.init \<^cterm>\<open>Trueprop (\<forall>x::real. x^2 - 2*x + 2 > 0)\<close>
val _ = time_tac "nbe(x^4+1>0)" (sturm_nbe_tac \<^context> 1) g5
val _ = time_tac "nbe(x^6+x^2+1>0)" (sturm_nbe_tac \<^context> 1) g6
val _ = time_tac "nbe(x^2-2x+2>0)" (sturm_nbe_tac \<^context> 1) g7
\<close>

section \<open>Failure case timing with NBE variant\<close>

ML \<open>
val _ = writeln "=== NBE failure cases ==="
val gf1 = Goal.init \<^cterm>\<open>Trueprop (\<forall>x::real. x^2 \<ge> 0)\<close>
val gf2 = Goal.init \<^cterm>\<open>Trueprop (\<exists>x::real. x^2 - 2 = 0)\<close>
val _ = time_tac "nbe_fail(geq)" (sturm_nbe_tac \<^context> 1) gf1
val _ = time_tac "nbe_fail(exists)" (sturm_nbe_tac \<^context> 1) gf2
\<close>

end
