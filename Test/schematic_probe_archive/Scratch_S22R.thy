theory Scratch_S22R
  imports Minilang.Minilang
begin

(* S22 matrix RE-RUN (S22R) on the NEW SUFFICES' code:
   - commit 75a65a7: SUFFICES' objectifies the leading subgoal with
     Object_Logic.full_atomize_tac before building the obligation P --> G;
   - TODAY: the schematic-variable rejection guard (has_schematic_vars) was
     DELETED, so schematic goals flow through SUFFICES unguarded.
   Measure soundness of SUFFICES on schematic-variable goals.

   READ-ONLY probe: no edits to proof.ML.  Uses the U8-repaired harness
   (Variable.declare_term is essential so fixed frees keep real types). *)

axiomatization PP :: "nat \<Rightarrow> bool" and QQ :: "nat \<Rightarrow> bool"
           and RR :: "nat \<Rightarrow> bool" where
  probe_rule_2: "PP n \<Longrightarrow> QQ n" and
  pp7: "PP 7" and
  rr_all: "RR n"

ML \<open>
(* ---- U8-repaired harness (copied exactly) -------------------------- *)
val base_ctxt = Named_Target.theory_init \<^theory>
fun schematic_ctxt ctxt = Proof_Context.set_mode Proof_Context.mode_schematic ctxt
fun mk_state' fixes prop_str =
  let val ctxt0 = #2 (Variable.add_fixes fixes base_ctxt)
      val t  = Syntax.read_prop (schematic_ctxt ctxt0) prop_str
      val ctxt = Variable.declare_term t ctxt0
      val ct = Thm.cterm_of ctxt t
   in Minilang.INIT ctxt (Goal.init ct) end
fun run script s = Minilang.parse_cmds (Minilang.lex_cmds script) s

(* Same body as mk_state', but also returns the read goal term and the
   INIT context, for the acceptance checks of the full-run subset. *)
fun mk_triple fixes prop_str =
  let val ctxt0 = #2 (Variable.add_fixes fixes base_ctxt)
      val t  = Syntax.read_prop (schematic_ctxt ctxt0) prop_str
      val ctxt = Variable.declare_term t ctxt0
      val ct = Thm.cterm_of ctxt t
   in (ctxt, t, Minilang.INIT ctxt (Goal.init ct)) end

(* ---- reporting ----------------------------------------------------- *)
fun vars_str s =
  let val (vs, tvs) = Minilang.schematic_vars_of_goal true s
      val ctxt = Minilang.context_of s
      val vstr = map (fn (xi, T) =>
                    Term.string_of_vname xi ^ " :: " ^
                    Syntax.string_of_typ ctxt T) vs
      val tstr = map (fn (xi, _) => "?'" ^ #1 xi) tvs
   in "TVars=[" ^ commas tstr ^ "]  Vars=[" ^ commas vstr ^ "]" end

fun goals_str s =
  let val ctxt = Minilang.context_of s
   in (case try Minilang.leading_proof_sequent_of s of
         NONE => "  <no sequent>"
       | SOME st =>
           (case Minilang.goals_of' st of
              [] => "  <0 subgoals>"
            | gs => cat_lines (map_index (fn (i, g) =>
                      "  goal " ^ string_of_int (i+1) ^ ". " ^
                      Syntax.string_of_term ctxt g) gs)))
  end

fun show label s =
  writeln (label ^ "\n  " ^ vars_str s ^ "\n" ^ goals_str s)

fun exn_str exn =
  case exn of
    Minilang.OPR_FAIL (_, m) => "[OPR_FAIL] " ^ m
  | _ => "[EXN] " ^ Runtime.exn_message exn

fun catching label f =
  case Exn.capture f () of
    Exn.Res r => SOME r
  | Exn.Exn exn =>
      if Exn.is_interrupt exn then Exn.reraise exn
      else (writeln (label ^ "  FAIL " ^ exn_str exn); NONE)

(* Open-only probe: run script, print PASS + resulting state or FAIL + exn. *)
fun probe_fix fixes label prop_str script =
  case catching label (fn () => run script (mk_state' fixes prop_str))
    of SOME s => show (label ^ "  PASS goal=" ^ prop_str ^ "  script=" ^ script) s
     | NONE => ()
fun probe label prop_str script = probe_fix [] label prop_str script

(* ---- acceptance checks for the full-run subset --------------------- *)

(* Is `obj` an instance of `pat` (schematics of pat instantiated)?
   Pattern.matches first; Unify.matchers as fallback for non-pattern
   shapes like ?f 7. *)
fun is_instance ctxt pat obj =
  (case try (fn () => Pattern.matches (Proof_Context.theory_of ctxt) (pat, obj)) () of
     SOME true => "YES(pattern)"
   | _ =>
      (case try (fn () =>
              is_some (Seq.pull (Unify.matchers (Context.Proof ctxt) [(pat, obj)]))) () of
         SOME true => "YES(unify)"
       | SOME false => "NO - NOT AN INSTANCE"
       | NONE => "CHECK-RAISED"))

fun probe_final fixes label prop_str script =
  case catching label (fn () =>
        let val (ctxt, t, s0) = mk_triple fixes prop_str
         in (ctxt, t, run script s0) end)
    of NONE => ()
     | SOME (ctxt, t, s) =>
        (show (label ^ "  PASS goal=" ^ prop_str ^ "  script=" ^ script) s;
         case catching (label ^ " conclude") (fn () => Minilang.conclude ctxt s)
           of NONE => ()
            | SOME th =>
                let (* Minilang.conclude keeps the Pure.prop goal protector on
                       the result; strip it before comparing with the original
                       statement. *)
                    val prop = perhaps (try Logic.unprotect) (Thm.prop_of th)
                 in writeln ("  RESULT THM: " ^ Syntax.string_of_term ctxt prop);
                    writeln ("  INSTANCE-OF-ORIGINAL: " ^ is_instance ctxt t prop);
                    writeln ("  hyps=" ^ string_of_int (length (Thm.hyps_of th)) ^
                             " tpairs=" ^ string_of_int (length (Thm.tpairs_of th)) ^
                             " extra_shyps=" ^ \<^make_string> (Thm.extra_shyps th));
                    (case try (fn () => Thm_Deps.all_oracles [th]) () of
                       SOME [] => writeln "  oracles: EMPTY"
                     | SOME ora => writeln ("  oracles: NONEMPTY " ^ \<^make_string> ora)
                     | NONE => writeln "  oracles: <all_oracles raised>")
                 end)
\<close>

ML \<open>writeln "======== GROUP A: controls, no schematics ========"\<close>

ML \<open>probe "A1 plain conclusion" "QQ (7::nat)" "SUFFICES \"PP (7::nat)\"";\<close>
ML \<open>probe "A2 meta-premise, no schematic" "PP (7::nat) \<Longrightarrow> QQ 7" "SUFFICES \"PP (7::nat)\"";\<close>
ML \<open>probe "A3 \<And>-binder, no schematic" "\<And>y. PP y \<Longrightarrow> QQ y" "SUFFICES \"\<forall>y. PP y \<longrightarrow> QQ y\"";\<close>
ML \<open>probe "A4 \<And>-binder identity (old path crashed)" "\<And>y. PP y \<Longrightarrow> PP y" "SUFFICES \"True\"";\<close>

ML \<open>writeln "======== GROUP B: schematic in conclusion only ========"\<close>

ML \<open>probe "B1 ?x argument position" "QQ (?x::nat)" "SUFFICES \"PP (7::nat)\"";\<close>
ML \<open>probe "B2 ?x twice in conjunction" "QQ (?x::nat) \<and> RR ?x" "SUFFICES \"PP (7::nat)\"";\<close>
ML \<open>probe "B3 function-typed ?f in conclusion" "QQ (?f (7::nat))" "SUFFICES \"PP (7::nat)\"";\<close>
ML \<open>probe "B4 predicate-head ?P" "(?P :: nat \<Rightarrow> bool) 7" "SUFFICES \"PP (7::nat)\"";\<close>
ML \<open>probe "B5 ?x both sides of =" "?x + 0 = (?x::nat)" "SUFFICES \"True\"";\<close>

ML \<open>writeln "======== GROUP C: schematic under structure ========"\<close>

ML \<open>probe "C1 clean premise, ?x conclusion" "PP (7::nat) \<Longrightarrow> QQ ?x" "SUFFICES \"PP (7::nat)\"";\<close>
ML \<open>probe "C2 \<And>-binder, ?x conclusion" "\<And>y. PP y \<Longrightarrow> QQ (?x::nat)" "SUFFICES \"QQ (7::nat)\"";\<close>
ML \<open>probe "C3 ?x premise only (RevB1 B1a)" "PP ?x \<Longrightarrow> RR 3" "SUFFICES \"RR (3::nat)\"";\<close>
ML \<open>probe "C4 ?x under nested meta-implication premise" "(PP ?x \<Longrightarrow> RR 3) \<Longrightarrow> RR 3" "SUFFICES \"RR (3::nat)\"";\<close>
ML \<open>probe "C5 ?x under \<exists>" "\<exists>y::nat. y = ?x" "SUFFICES \"True\"";\<close>
ML \<open>probe "C6 schematic in the SUFFICES prop itself" "QQ (?x::nat)" "SUFFICES \"QQ ?z\"";\<close>

ML \<open>writeln "======== GROUP D: NEW ROWS premise+conclusion schematics ========"\<close>

ML \<open>probe "D1 SAME ?x premise and conclusion" "PP ?x \<Longrightarrow> QQ ?x" "SUFFICES \"True\"";\<close>
ML \<open>probe "D2 DIFFERENT ?x/?y premise vs conclusion" "PP ?x \<Longrightarrow> QQ ?y" "SUFFICES \"True\"";\<close>

ML \<open>writeln "======== GROUP E: NEW ROWS schematic TYPE variables ========"\<close>

ML \<open>probe_fix ["x"] "E1 TVar only: (x::?'a) = x" "(x::?'a) = x" "SUFFICES \"True\"";\<close>
ML \<open>probe "E2 TVar + Var mixed: (?y::?'a) = ?y" "(?y::?'a) = ?y" "SUFFICES \"True\"";\<close>
ML \<open>probe_fix ["x"] "E3 TVar in conclusion, ?x::nat in premise" "PP ?x \<Longrightarrow> (x::?'a) = x" "SUFFICES \"True\"";\<close>

ML \<open>writeln "======== GROUP F: multiple subgoals (sibling present) ========"\<close>

ML \<open>probe "F1 SPLIT then SUFFICES, shared ?x sibling (open)" "QQ (?x::nat) \<and> RR ?x"
      "SPLIT_CONJS SUFFICES \"PP (7::nat)\"";\<close>
ML \<open>probe "F1b same, obligation proved + END: watch sibling" "QQ (?x::nat) \<and> RR ?x"
      "SPLIT_CONJS SUFFICES \"PP (7::nat)\" APPLY (intro impI) APPLY (rule probe_rule_2) APPLY (assumption) END";\<close>
ML \<open>probe "F3 control: SPLIT then SUFFICES, no schematic" "QQ (7::nat) \<and> RR 3"
      "SPLIT_CONJS SUFFICES \"PP (7::nat)\"";\<close>

ML \<open>writeln "======== GROUP H: structured SUFFICES (if/for) on schematic goal ========"\<close>

ML \<open>probe "H1 SUFFICES with for-fix on ?x goal" "QQ (?x::nat)" "SUFFICES \"QQ x\" for x :: nat";\<close>
ML \<open>probe "H2 SUFFICES with if-premise on ?x goal" "QQ (?x::nat)" "SUFFICES \"QQ (7::nat)\" if h: \"PP (7::nat)\"";\<close>

ML \<open>writeln "======== GROUP M: meta-equality goal ========"\<close>

ML \<open>probe_fix ["x"] "M1 meta-eq goal (x::nat) \<equiv> x" "(x::nat) \<equiv> x" "SUFFICES \"True\"";\<close>

ML \<open>writeln "======== FULL-RUN SUBSET (conclude + acceptance checks) ========"\<close>

ML \<open>probe_final [] "FR-A1 control conclusion" "QQ (7::nat)"
  "SUFFICES \"PP (7::nat)\" APPLY (intro impI) APPLY (rule probe_rule_2) APPLY (assumption) END APPLY (rule pp7) END";\<close>

ML \<open>probe_final [] "FR-A3 control \<And>-binder" "\<And>y. PP y \<Longrightarrow> QQ y"
  "SUFFICES \"\<forall>y. PP y \<longrightarrow> QQ y\" APPLY (intro impI) APPLY (assumption) END APPLY (intro allI impI) APPLY (rule probe_rule_2) APPLY (assumption) END";\<close>

ML \<open>probe_final [] "FR-B1 ?x conclusion" "QQ (?x::nat)"
  "SUFFICES \"PP (7::nat)\" APPLY (intro impI) APPLY (rule probe_rule_2) APPLY (assumption) END APPLY (rule pp7) END";\<close>

ML \<open>probe_final [] "FR-B3 function-typed ?f" "QQ (?f (7::nat))"
  "SUFFICES \"PP (7::nat)\" APPLY (intro impI) APPLY (rule probe_rule_2) APPLY (assumption) END APPLY (rule pp7) END";\<close>

ML \<open>probe_final [] "FR-B4 predicate-head ?P" "(?P :: nat \<Rightarrow> bool) 7"
  "SUFFICES \"PP (7::nat)\" APPLY (intro impI) APPLY (assumption) END APPLY (rule pp7) END";\<close>

ML \<open>probe_final [] "FR-B5 ?x kept UNpinned" "?x + 0 = (?x::nat)"
  "SUFFICES \"True\" APPLY (intro impI) APPLY (rule add_0_right) END APPLY (rule TrueI) END";\<close>

ML \<open>probe_final [] "FR-C1 clean premise, ?x conclusion" "PP (7::nat) \<Longrightarrow> QQ ?x"
  "SUFFICES \"PP (7::nat)\" APPLY (intro impI) APPLY (rule probe_rule_2) APPLY (assumption) END APPLY (rule pp7) END";\<close>

ML \<open>probe_final [] "FR-C2 \<And>-binder, ?x conclusion" "\<And>y. PP y \<Longrightarrow> QQ (?x::nat)"
  "SUFFICES \"QQ (7::nat)\" APPLY (intro impI allI) APPLY (assumption) END APPLY (rule probe_rule_2) APPLY (rule pp7) END";\<close>

ML \<open>probe_final [] "FR-C3 ?x premise only" "PP ?x \<Longrightarrow> RR 3"
  "SUFFICES \"RR (3::nat)\" APPLY (intro impI) APPLY (assumption) END APPLY (rule rr_all) END";\<close>

ML \<open>probe_final [] "FR-D1 SAME ?x both sides" "PP ?x \<Longrightarrow> QQ ?x"
  "SUFFICES \"True\" APPLY (intro impI) APPLY (rule probe_rule_2) APPLY (assumption) END APPLY (rule TrueI) END";\<close>

ML \<open>probe_final [] "FR-D2 DIFFERENT ?x/?y" "PP ?x \<Longrightarrow> QQ ?y"
  "SUFFICES \"True\" APPLY (intro impI) APPLY (rule probe_rule_2) APPLY (assumption) END APPLY (rule TrueI) END";\<close>

ML \<open>probe_final ["x"] "FR-E1 TVar goal (x::?'a) = x" "(x::?'a) = x"
  "SUFFICES \"True\" APPLY (intro impI) APPLY (rule refl) END APPLY (rule TrueI) END";\<close>

ML \<open>probe_final [] "FR-F2 sibling subgoal, shared ?x" "QQ (?x::nat) \<and> RR ?x"
  "SPLIT_CONJS SUFFICES \"PP (7::nat)\" APPLY (intro impI) APPLY (rule probe_rule_2) APPLY (assumption) END APPLY (rule pp7) NEXT APPLY (rule rr_all) END";\<close>

ML \<open>probe_final [] "FR-H2 structured if on ?x goal" "QQ (?x::nat)"
  "SUFFICES \"QQ (7::nat)\" if h: \"PP (7::nat)\" APPLY (intro impI) APPLY (erule mp) APPLY (rule pp7) END APPLY (rule probe_rule_2) APPLY (rule pp7) END";\<close>

ML \<open>writeln "======== DEBUG: locate the failing step of FR-F2 and FR-H2 ========"\<close>

ML \<open>probe "F2s1 +APPLY (rule pp7)" "QQ (?x::nat) \<and> RR ?x"
  "SPLIT_CONJS SUFFICES \"PP (7::nat)\" APPLY (intro impI) APPLY (rule probe_rule_2) APPLY (assumption) END APPLY (rule pp7)";\<close>
ML \<open>probe "F2s2 +APPLY (rule rr_all)" "QQ (?x::nat) \<and> RR ?x"
  "SPLIT_CONJS SUFFICES \"PP (7::nat)\" APPLY (intro impI) APPLY (rule probe_rule_2) APPLY (assumption) END APPLY (rule pp7) APPLY (rule rr_all)";\<close>

ML \<open>probe "H2s1 +APPLY (intro impI)" "QQ (?x::nat)"
  "SUFFICES \"QQ (7::nat)\" if h: \"PP (7::nat)\" APPLY (intro impI)";\<close>
ML \<open>probe "H2s2 +APPLY (erule mp)" "QQ (?x::nat)"
  "SUFFICES \"QQ (7::nat)\" if h: \"PP (7::nat)\" APPLY (intro impI) APPLY (erule mp)";\<close>
ML \<open>probe "H2s3 +APPLY (rule pp7)" "QQ (?x::nat)"
  "SUFFICES \"QQ (7::nat)\" if h: \"PP (7::nat)\" APPLY (intro impI) APPLY (erule mp) APPLY (rule pp7)";\<close>
ML \<open>probe "H2s4 +END" "QQ (?x::nat)"
  "SUFFICES \"QQ (7::nat)\" if h: \"PP (7::nat)\" APPLY (intro impI) APPLY (erule mp) APPLY (rule pp7) END";\<close>

ML \<open>writeln "======== extra_shyps CONTROLS (no schematics) ========"\<close>

ML \<open>probe_final [] "FR-A2ctl meta-premise control" "PP (7::nat) \<Longrightarrow> QQ 7"
  "SUFFICES \"PP (7::nat)\" APPLY (intro impI) APPLY (rule probe_rule_2) APPLY (assumption) END APPLY (rule pp7) END";\<close>
ML \<open>probe_final ["n"] "FR-B5ctl free-variable control" "n + 0 = (n::nat)"
  "SUFFICES \"True\" APPLY (intro impI) APPLY (rule add_0_right) END APPLY (rule TrueI) END";\<close>

end
