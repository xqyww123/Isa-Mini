theory My_Object_Logic_Acceptance_Test
  imports Minilang.Minilang
begin

(* Acceptance suite for the object-logic layer of My_Object_Logic
   (MY_OBJECT_LOGIC_PLAN.md section 8, items 2/3/8 unit level + K4 scan).
   NOT in ROOT: run manually after any change to my_object_logic.ML.

   Discipline (review A5): the target oracle below is a LOCAL copy, never
   imported from the implementation -- an implementation bug in its own
   target computation must not blind the suite.
   All terms are ML-built (Syntax.read_* eta-contracts at parse time);
   all comparisons are aconv / make_string dumps, never printed strings. *)

ML \<open>
val failures : string list Unsynchronized.ref = Unsynchronized.ref [];
fun fail msg = (writeln ("FAIL: " ^ msg); failures := msg :: !failures);
fun check name b = if b then () else fail name;
\<close>

section \<open>Corpus\<close>

ML \<open>
val ctxt = @{context};
val natT = @{typ nat};
val bT = @{typ bool};
val setT = @{typ "nat set"};
val Tp = HOLogic.mk_Trueprop;
val AA = Free ("AA", bT);
val BB = Free ("BB", bT);
val CC = Free ("CC", bT);
val PP = Free ("PP", natT --> bT);
val RR = Free ("RR", natT --> natT --> bT);
val PP2 = Free ("PP2", (natT --> bT) --> bT);
val SS = Free ("SS", setT);
val aF = Free ("a", natT);
val bF = Free ("b", natT);
val WF = Free ("W", propT);          (* prop-typed Free: unatomizable premise *)
val Wfun = Free ("W", natT --> propT);

fun allx nm body = HOLogic.mk_all (nm, natT, body);
fun mem x = Const (@{const_name Set.member}, natT --> setT --> bT) $ x $ SS;
fun ball body = Const (@{const_name Ball}, setT --> (natT --> bT) --> bT) $ SS $ body;
fun bex body = Const (@{const_name Bex}, setT --> (natT --> bT) --> bT) $ SS $ body;
fun propw t = Const (@{const_name Pure.prop}, propT --> propT) $ t;
fun termm t = Const (@{const_name Pure.term}, natT --> propT) $ t;
val ofcls = Logic.mk_of_class (natT, \<^class>\<open>ord\<close>);
val aTv = TVar (("'a", 0), \<^sort>\<open>ord\<close>);
val sortc = Const (@{const_name Pure.sort_constraint},
                   Term.itselfT aTv --> propT) $ Logic.mk_type aTv;
val QQv = Var (("Q", 0), natT --> bT);
val Pv = Var (("P", 0), bT);
val Wv = Var (("W", 0), propT);
val Qa = Free ("Qa", aTv --> bT);
val xa = Free ("x", aTv);

(* the original 8 feasibility-probe shapes *)
val probe_corpus = [
  ("t1_forall_eta",
     Logic.all aF (Logic.mk_implies (Tp (HOLogic.mk_conj (AA, BB)),
       Logic.mk_implies (Tp (allx "xx" (PP $ Bound 0)),
         Tp (HOLogic.mk_conj (PP $ aF, AA)))))),
  ("t2_simple_meta_all", Logic.all aF (Tp (PP $ aF))),
  ("t3_nested_meta", Logic.all aF (Logic.mk_implies
       (Logic.all bF (Tp (RR $ bF $ aF)), Tp AA))),
  ("t4_meta_conjunction", Logic.mk_conjunction (Tp AA, Tp BB)),
  ("t5_meta_eq", Logic.mk_equals (aF, bF)),
  ("t6_inner_lambda",
     Logic.all aF (Tp (PP2 $ Abs ("yy", natT, RR $ aF $ Bound 0)))),
  ("t7_already_contracted",
     Logic.all aF (Logic.mk_implies
       (Tp (Const (@{const_name All}, (natT --> bT) --> bT) $ PP), Tp AA))),
  ("t8_schematic",
     Logic.mk_implies (Tp (Var (("P", 0), bT)),
       Logic.mk_implies (Tp (allx "zz" (Var (("Q", 0), natT --> bT) $ Bound 0)),
         Tp (Var (("P", 0), bT)))))
];

(* t9 class (section 8-3): the system returns a REFLEXIVE equation whose rhs is
   not beta-eta normal -- the only shape on which a fallback that "helpfully"
   normalises is distinguishable from the correct verbatim fallback *)
val t9 = ("t9_reflexive_eta_redex", Logic.all aF (Wfun $ aF));

(* hand-picked adversarial corpus (33 shapes, review round) *)
val hand_corpus = [
  ("h01_ball_meta_form",       Logic.all aF (Logic.mk_implies (Tp (mem aF), Tp (PP $ aF)))),
  ("h02_ball_obj",             Tp (ball (Abs ("u", natT, PP $ Bound 0)))),
  ("h03_ball_obj_eta",         Tp (ball PP)),
  ("h04_bex_obj",              Tp (bex (Abs ("u", natT, PP $ Bound 0)))),
  ("h05_ball_under_meta",      Logic.mk_implies (Tp (ball (Abs ("u", natT, PP $ Bound 0))), Tp AA)),
  ("h06_nested_all_imp",
     Logic.all aF (Logic.mk_implies (Logic.all bF (Tp (RR $ aF $ bF)),
       Logic.mk_implies (Logic.mk_implies (Tp AA, Tp BB), Tp CC)))),
  ("h07_conj_assoc_L",         Logic.mk_conjunction (Logic.mk_conjunction (Tp AA, Tp BB), Tp CC)),
  ("h08_conj_assoc_R",         Logic.mk_conjunction (Tp AA, Logic.mk_conjunction (Tp BB, Tp CC))),
  ("h09_conj_under_all",
     Logic.all aF (Logic.mk_conjunction (Tp (PP $ aF), Tp AA))),
  ("h10_prop_atom",            propw (Tp AA)),
  ("h11_prop_imp",             propw (Logic.mk_implies (Tp AA, Tp BB))),
  ("h12_prop_all_eta",         propw (Logic.all aF (Tp (allx "u" (PP $ Bound 0))))),
  ("h13_prop_in_prem",         Logic.mk_implies (propw (Tp AA), Tp BB)),
  ("h14_all_over_prop",        Logic.all aF (propw (Tp (PP $ aF)))),
  ("h15_eq_prem_nat",          Logic.mk_implies (Logic.mk_equals (aF, bF), Tp AA)),
  ("h16_eq_prem_bool",         Logic.mk_implies (Logic.mk_equals (AA, BB), Tp CC)),
  ("h17_eq_prem_fun",
     Logic.mk_implies (Logic.mk_equals (PP, Abs ("u", natT, PP $ Bound 0)), Tp AA)),
  ("h18_propeq_prem",
     Logic.mk_implies (Logic.mk_equals (Tp AA, Tp BB), Tp CC)),
  ("h19_propeq_sides_atomizable",
     Logic.mk_equals (Logic.all aF (Tp (PP $ aF)), Tp AA)),
  ("h20_eq_conclusion",        Logic.mk_equals (AA, BB)),
  ("h21_var_content",          Logic.mk_implies (Tp Pv, Tp AA)),
  ("h22_var_prop_prem",        Logic.mk_implies (Wv, Tp AA)),
  ("h23_var_fun_under_all",    Logic.all aF (Tp (QQv $ aF))),
  ("h24_var_fun_eta_all",      Tp (allx "z" (QQv $ Bound 0))),
  ("h25_tvar_sorted",          Logic.all xa (Tp (Qa $ xa))),
  ("h26_sort_constraint_prem", Logic.mk_implies (sortc, Tp AA)),
  ("h27_partial_free_prop",    Logic.all aF (Logic.mk_implies (WF, Tp (PP $ aF)))),
  ("h28_partial_ofclass",      Logic.mk_implies (ofcls, Tp AA)),
  ("h29_ofclass_concl",        Logic.mk_implies (Tp AA, ofcls)),
  ("h30_term_marker_conj",     Logic.mk_conjunction (termm aF, Tp AA)),
  ("h31_deep_mix",
     Logic.all aF (Logic.mk_implies (Logic.all bF (Tp (RR $ bF $ aF)),
       Logic.mk_implies (Logic.mk_implies (Tp AA, Tp (allx "v" (PP $ Bound 0))),
         Logic.mk_conjunction (Tp (PP $ aF), Tp BB))))),
  ("h32_vacuous_all",          Logic.all (Free ("unused", natT)) (Tp AA)),
  ("h33_conj_of_alls_eta",
     Logic.mk_conjunction (Tp (allx "p" (PP $ Bound 0)), Logic.all aF (Tp (PP $ aF))))
];

(* skeleton-enumeration generator (review round; same leaves and kernels) *)
val leaves = [
  ("L_tpAA",      Tp AA),
  ("L_tpPa",      Tp (PP $ aF)),
  ("L_tpRab",     Tp (RR $ aF $ bF)),
  ("L_tpAllEta",  Tp (allx "u" (PP $ Bound 0))),
  ("L_tpAllCon",  Tp (Const (@{const_name All}, (natT --> bT) --> bT) $ PP)),
  ("L_tpBall",    Tp (ball (Abs ("u", natT, RR $ aF $ Bound 0)))),
  ("L_eqNat",     Logic.mk_equals (aF, bF)),
  ("L_eqBool",    Logic.mk_equals (AA, BB)),
  ("L_varProp",   Wv),
  ("L_termM",     termm aF),
  ("L_ofclass",   ofcls),
  ("L_freeProp",  WF)
];

fun binaries lvl ts us =
  maps (fn (n1, t1) => maps (fn (n2, t2) =>
    [(lvl ^ "_imp(" ^ n1 ^ "," ^ n2 ^ ")", Logic.mk_implies (t1, t2)),
     (lvl ^ "_cnj(" ^ n1 ^ "," ^ n2 ^ ")", Logic.mk_conjunction (t1, t2)),
     (lvl ^ "_peq(" ^ n1 ^ "," ^ n2 ^ ")", Logic.mk_equals (t1, t2))]) us) ts;

fun unaries lvl ts =
  maps (fn (n, t) =>
    [(lvl ^ "_allA(" ^ n ^ ")", Logic.all aF t),
     (lvl ^ "_allB(" ^ n ^ ")", Logic.all bF t),
     (lvl ^ "_prp(" ^ n ^ ")", propw t)]) ts;

val level1 = binaries "d1" leaves leaves @ unaries "d1" leaves;
val kernel_names =
  ["d1_imp(L_tpPa,L_tpAllEta)", "d1_imp(L_tpAllEta,L_tpPa)", "d1_cnj(L_tpPa,L_tpAA)",
   "d1_imp(L_eqNat,L_tpAA)", "d1_imp(L_varProp,L_tpPa)", "d1_cnj(L_termM,L_tpAA)",
   "d1_allA(L_tpPa)", "d1_allB(L_tpRab)", "d1_prp(L_tpAA)", "d1_imp(L_ofclass,L_tpAA)",
   "d1_peq(L_tpAA,L_tpAA)", "d1_imp(L_tpBall,L_tpAA)"];
val kernel = filter (fn (n, _) => member (op =) kernel_names n) level1;
val level2 = binaries "d2" kernel leaves @ binaries "d2r" leaves kernel @ unaries "d2" level1;
val level3 = unaries "d3" (binaries "k" kernel kernel);
val corpus_gen = level1 @ level2 @ level3;

val corpus_all = probe_corpus @ hand_corpus @ corpus_gen;
val _ = writeln ("CORPUS: " ^ string_of_int (length corpus_all) ^ " shapes");

(* the acceptance oracle: LOCAL target rebuild, independent of the facade *)
fun oracle_target t =
  let val t0 = Object_Logic.atomize_term ctxt t
  in if fastype_of t0 = bT then Tp t0 else t0 end;
\<close>

section \<open>8-2: facade sweep -- every shape, output aconv the oracle target\<close>

ML \<open>
val _ = My_Object_Logic.reset_census ();

fun sweep (nm, t) =
  \<^try>\<open>
    let
      val ct = Thm.cterm_of ctxt t;
      val eq = My_Object_Logic.atomize_conv {strict = false} ctxt ct;
      val lhs_ok = Thm.term_of (Thm.lhs_of eq) aconv t;
      val rhs = Thm.term_of (Thm.rhs_of eq);
      val target = oracle_target t;
      val rhs_ok = rhs aconv target;
      val _ = if lhs_ok then () else fail (nm ^ ": conv lhs <> input");
      val _ = if rhs_ok then () else
        fail (nm ^ ": output <> target\n  GOT  " ^ @{make_string} rhs ^
              "\n  WANT " ^ @{make_string} target);
    in rhs_ok end
    catch exn => (fail (nm ^ ": EXCEPTION " ^ @{make_string} exn); false)\<close>;

val sweep_results = map sweep corpus_all;
val {intact, repaired, fallback} = My_Object_Logic.census ();
val _ = writeln ("SWEEP: " ^ string_of_int (length corpus_all) ^ " shapes, ok=" ^
                 string_of_int (length (filter I sweep_results)) ^
                 "; census intact=" ^ string_of_int intact ^
                 " repaired=" ^ string_of_int repaired ^
                 " fallback=" ^ string_of_int fallback);
(* red lines: no fallback ever; and the corpus must still contain shapes the
   system damages (repaired > 0), else the trimming rule of 8-2 is violated *)
val _ = check "census: fallback must be 0" (fallback = 0);
val _ = check "corpus red line: no damaged (identical=false) shapes left" (repaired > 0);
\<close>

section \<open>8-2: K4 standing assertion -- fast path never hides binder-name loss\<close>

ML \<open>
fun binder_names (Abs (n, _, b)) = n :: binder_names b
  | binder_names (f $ x) = binder_names f @ binder_names x
  | binder_names _ = [];

fun k4_scan (nm, t) =
  let
    val target = oracle_target t;
    val damaged = Thm.term_of (Thm.rhs_of (Object_Logic.atomize ctxt (Thm.cterm_of ctxt t)));
  in
    if damaged aconv target then
      (if binder_names target = binder_names damaged then SOME true
       else (fail ("K4 counterexample " ^ nm); SOME false))
    else NONE  (* fast path not taken: irrelevant to K4 *)
  end;

val k4_results = map_filter I (map k4_scan corpus_all);
val _ = writeln ("K4 SCAN: identical-branch samples=" ^ string_of_int (length k4_results) ^
                 " counterexamples=" ^ string_of_int (length (filter not k4_results)));
\<close>

section \<open>8-3: injection tests of the exported repair core\<close>

ML \<open>
(* fallback branch: a fake (mismatching) target must return the system
   equation VERBATIM -- same prop, hyps and shyps *)
fun same_thm th1 th2 =
  Thm.full_prop_of th1 aconv Thm.full_prop_of th2
  andalso eq_list (op aconv) (Thm.hyps_of th1, Thm.hyps_of th2)
  andalso eq_set (op =) (Thm.shyps_of th1, Thm.shyps_of th2);

val fake_target = Tp (Free ("TOTALLY_WRONG", bT));

fun inject (nm, t) =
  let
    val eq_sys = Object_Logic.atomize ctxt (Thm.cterm_of ctxt t);
    val fb = My_Object_Logic.repair_or_fallback ctxt eq_sys fake_target;
  in check ("8-3 fallback verbatim: " ^ nm) (same_thm fb eq_sys) end;

(* t1: representative damaged shape; t9: rhs of the system equation is NOT
   beta-eta normal, so a fallback that normalises on the way out is caught *)
val _ = inject (hd probe_corpus);
val _ = inject t9;
val _ =
  let val (_, t) = t9
      val eq_sys = Object_Logic.atomize ctxt (Thm.cterm_of ctxt t)
  in check "t9 preconditions: system equation reflexive, rhs non-normal"
       (Thm.term_of (Thm.rhs_of eq_sys) aconv t
        andalso not (Envir.beta_eta_contract t aconv t))
  end;
\<close>

ML \<open>
(* mutation audit: the section 4A.1 skeleton, parameterised; each mutant class
   must be caught by at least one criterion above (emulated here) *)
fun mk_atomize_conv {target_of, combine, fallback} ctxt ct =
  let
    val eq = Object_Logic.atomize ctxt ct;
    val damaged = Thm.term_of (Thm.rhs_of eq);
    val target = target_of (Thm.term_of ct);
  in
    if damaged aconv target then eq
    else if Envir.beta_eta_contract damaged aconv Envir.beta_eta_contract target
    then combine ctxt eq target
    else fallback ctxt eq ct
  end;

fun combine_correct ctxt eq target =
  let
    val eq_t = Drule.beta_eta_conversion (Thm.cterm_of ctxt target);
    val eq_d = Drule.beta_eta_conversion (Thm.rhs_of eq);
  in Thm.transitive eq (Thm.transitive eq_d (Thm.symmetric eq_t)) end;
fun combine_flipped ctxt eq target =        (* mutant b: transitive misassembled *)
  let
    val eq_t = Drule.beta_eta_conversion (Thm.cterm_of ctxt target);
    val eq_d = Drule.beta_eta_conversion (Thm.rhs_of eq);
  in Thm.transitive eq (Thm.transitive eq_t (Thm.symmetric eq_d)) end;
fun target_no_tp t = Object_Logic.atomize_term ctxt t;   (* mutant a: Trueprop forgotten *)
fun fallback_correct _ eq _ = eq;
fun fallback_half ctxt _ ct =               (* mutant c: fallback normalises *)
  Drule.beta_eta_conversion (Thm.cterm_of ctxt (Thm.term_of ct));

fun sweep_red name conv corpus =
  let
    fun one (_, t) =
      \<^try>\<open>
        let val eq = conv ctxt (Thm.cterm_of ctxt t)
        in Thm.term_of (Thm.rhs_of eq) aconv oracle_target t
           andalso Thm.term_of (Thm.lhs_of eq) aconv t end
        catch _ => false\<close>;
    val greens = length (filter I (map one corpus));
  in greens < length corpus end;  (* true = the suite catches the mutant *)

val va = mk_atomize_conv {target_of = target_no_tp, combine = combine_correct, fallback = fallback_correct};
val vb = mk_atomize_conv {target_of = oracle_target, combine = combine_flipped, fallback = fallback_correct};
val _ = check "mutant a (no Trueprop) caught by 8-2 sweep" (sweep_red "va" va corpus_all);
val _ = check "mutant b (flipped transitive) caught by 8-2 sweep" (sweep_red "vb" vb corpus_all);

(* mutant c is invisible to the 8-2 sweep (fallback never fires there); the
   t9 injection is what catches it *)
fun inject_catches fb_impl =
  let
    val (_, t) = t9;
    val eq_sys = Object_Logic.atomize ctxt (Thm.cterm_of ctxt t);
    fun repair_mut ctxt eq target =
      let val damaged = Thm.term_of (Thm.rhs_of eq) in
        if damaged aconv target then eq
        else if Envir.beta_eta_contract damaged aconv Envir.beta_eta_contract target
        then combine_correct ctxt eq target
        else fb_impl ctxt eq (Thm.cterm_of ctxt t)
      end;
  in not (same_thm (repair_mut ctxt eq_sys fake_target) eq_sys) end;
val _ = check "mutant c (normalising fallback) caught by t9 injection" (inject_catches fallback_half);

(* mutant e: guard removed -- repair attempted on a genuine mismatch; the
   kernel's transitive middle-term check must make it raise, not mis-repair *)
val _ =
  let
    val (_, t) = hd probe_corpus;
    val eq_sys = Object_Logic.atomize ctxt (Thm.cterm_of ctxt t);
    val caught = (combine_correct ctxt eq_sys fake_target; false)
                 handle THM _ => true;
  in check "mutant e (guard removed) caught by kernel THM exception" caught end;
\<close>

section \<open>8-8 unit level: {strict} semantics\<close>

ML \<open>
(* complete input: strict and tolerant agree exactly *)
val _ =
  let
    val (_, t) = hd probe_corpus;
    val ct = Thm.cterm_of ctxt t;
    val eq_s = My_Object_Logic.atomize_conv {strict = true} ctxt ct;
    val eq_n = My_Object_Logic.atomize_conv {strict = false} ctxt ct;
  in check "strict = tolerant on complete input" (same_thm eq_s eq_n) end;

(* incomplete input: strict raises CTERM "Fail to atomize" with the INPUT as
   payload (phi semantics verbatim); tolerant returns the best effort *)
val incomplete = [t9, ("h22", Logic.mk_implies (Wv, Tp AA)),
                  ("h27", Logic.all aF (Logic.mk_implies (WF, Tp (PP $ aF))))];
val _ = List.app (fn (nm, t) =>
  let
    val ct = Thm.cterm_of ctxt t;
    val _ = \<^try>\<open>(My_Object_Logic.atomize_conv {strict = false} ctxt ct; ())
            catch exn => fail ("tolerant raised on incomplete " ^ nm ^ ": " ^ @{make_string} exn)\<close>;
    val ok = (My_Object_Logic.atomize_conv {strict = true} ctxt ct; false)
             handle CTERM ("Fail to atomize", [pay]) => Thm.term_of pay aconv t;
  in check ("strict raises CTERM with input payload: " ^ nm) ok end) incomplete;

(* term level: strict failure is TERM "Fail to atomize"; tolerant is verbatim *)
val _ =
  let
    val (_, t) = t9;
    val ok = (My_Object_Logic.atomize_term {strict = true} ctxt t; false)
             handle TERM ("Fail to atomize", _) => true;
    val same = My_Object_Logic.atomize_term {strict = false} ctxt t
               aconv Object_Logic.atomize_term ctxt t;
  in check "strict atomize_term raises TERM" ok;
     check "tolerant atomize_term = system atomize_term" same
  end;

(* Trueprop short circuit holds in both modes *)
val _ =
  let
    val ct = Thm.cterm_of ctxt (Tp AA);
    val ok = Thm.is_reflexive (My_Object_Logic.atomize_conv {strict = true} ctxt ct)
             andalso Thm.is_reflexive (My_Object_Logic.atomize_conv {strict = false} ctxt ct);
  in check "Trueprop short circuit in both modes" ok end;

(* tactic level: CONVERSION maps the strict CTERM to an EMPTY result sequence.
   This is what the two full_atomize_tac sites lean on for presentation:
   SUFFICES (proof.ML) sees Seq.pull = NONE and falls back to the raw state;
   the AoA subgoal merge (agent_server.ML) sees SINGLE = NONE and raises its
   readable Agent_Give_Up.  Neither lets the exception escape. *)
val _ =
  let
    val (_, t) = t9;
    val st = Goal.init (Thm.cterm_of ctxt (Logic.mk_implies (t, Tp AA)));
    val strict_empty =
      (case Seq.pull (My_Object_Logic.full_atomize_tac {strict = true} ctxt 1 st)
         of NONE => true | SOME _ => false);
    val tolerant_some =
      (case Seq.pull (My_Object_Logic.full_atomize_tac {strict = false} ctxt 1 st)
         of SOME _ => true | NONE => false);
  in check "strict full_atomize_tac yields empty Seq on incomplete subgoal" strict_empty;
     check "tolerant full_atomize_tac still progresses" tolerant_some
  end;
\<close>

section \<open>Verdict\<close>

ML \<open>
val _ =
  if null (!failures) then writeln "ACCEPTANCE: ALL GREEN"
  else error ("ACCEPTANCE: " ^ string_of_int (length (!failures)) ^ " failure(s):\n  " ^
              cat_lines (rev (!failures)));
\<close>

end
