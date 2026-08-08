theory Scratch_SchematicProbe
  imports Minilang.Minilang
begin

axiomatization PP :: "nat \<Rightarrow> bool" and QQ :: "nat \<Rightarrow> bool" where
  probe_rule_2: "PP n \<Longrightarrow> QQ n"

lemma probe_rule_1: "PP (7::nat) \<Longrightarrow> QQ (7::nat)" by (rule probe_rule_2)

definition FOO :: "nat \<Rightarrow> nat" where "FOO n = n + 1"

ML \<open>
(* ---- probe harness ------------------------------------------------- *)

val base_ctxt = Named_Target.theory_init \<^theory>

fun fix_ctxt fixes ctxt = #2 (Variable.add_fixes fixes ctxt)

fun schematic_ctxt ctxt = Proof_Context.set_mode Proof_Context.mode_schematic ctxt

(* `fixes`: free variables of the goal, fixed in the context the way a
   real `lemma` would fix them. *)
fun mk_state' fixes prop_str =
  let val ctxt  = fix_ctxt fixes base_ctxt
      val t  = Syntax.read_prop (schematic_ctxt ctxt) prop_str
      val ct = Thm.cterm_of ctxt t
   in Minilang.INIT ctxt (Goal.init ct) end

fun mk_state prop_str = mk_state' [] prop_str

fun run script s = Minilang.parse_cmds (Minilang.lex_cmds script) s

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

fun sequent_str s =
  let val ctxt = Minilang.context_of s
   in (case try Minilang.leading_proof_sequent_of s of
         NONE => "  SEQUENT: <none>"
       | SOME st => "  SEQUENT: " ^ Syntax.string_of_term ctxt (Thm.prop_of st))
  end

fun show label s =
  writeln (label ^ "\n  " ^ vars_str s ^ "\n" ^ goals_str s ^ "\n" ^ sequent_str s)

fun show_full label s =
  (show label s;
   writeln ("  RAW STATE (whole stack): " ^ \<^make_string> s))

fun exn_str exn =
  case exn of
    Minilang.OPR_FAIL (_, m) => "[OPR_FAIL] " ^ m
  | _ => "[EXN] " ^ Runtime.exn_message exn

fun catching label f =
  case Exn.capture f () of
    Exn.Res r => SOME r
  | Exn.Exn exn =>
      if Exn.is_interrupt exn then Exn.reraise exn
      else (writeln (label ^ "  " ^ exn_str exn); NONE)

fun probe_fix fixes label prop_str script =
  case catching label (fn () => run script (mk_state' fixes prop_str))
    of SOME s => show (label ^ "  [OK] goal=" ^ prop_str ^ "  script=" ^ script) s
     | NONE => ()

fun probe label prop_str script = probe_fix [] label prop_str script

fun probe_full label prop_str script =
  case catching label (fn () => run script (mk_state prop_str))
    of SOME s => show_full (label ^ "  [OK] goal=" ^ prop_str ^ "  script=" ^ script) s
     | NONE => ()

fun probe' label s0 script =
  case catching label (fn () => run script s0)
    of SOME s => (show (label ^ "  [OK] script=" ^ script) s; SOME s)
     | NONE => NONE

fun probe_final label prop_str script =
  case catching label (fn () => run script (mk_state prop_str))
    of SOME s =>
        (show (label ^ "  [OK] goal=" ^ prop_str ^ "  script=" ^ script) s;
         case catching (label ^ " conclude") (fn () => Minilang.conclude base_ctxt s)
           of SOME th => writeln ("  RESULT THM: " ^
                 Syntax.string_of_term base_ctxt (Thm.prop_of th))
            | NONE => ())
     | NONE => ()
\<close>

ML \<open>writeln "======== GROUP 1: RULE ========"\<close>

ML \<open>
probe "R1 RULE forcing rule, 1 subgoal" "QQ (?x::nat)" "RULE probe_rule_1";
probe "R2 RULE sym, 1 subgoal, no forcing" "?x + 0 = (?x::nat)" "RULE sym";
probe "R3 RULE insertI1" "(?x::nat) \<in> {1,2,3}" "RULE insertI1";
probe "R4 RULE insertI2" "(?x::nat) \<in> {1,2,3}" "RULE insertI2";
probe "R5 RULE generic rule probe_rule_2" "QQ (?x::nat)" "RULE probe_rule_2";
probe "R6 RULE exI (schematic witness)" "\<exists>y::nat. y = ?x" "RULE exI";
\<close>

ML \<open>writeln "======== GROUP 1b: RULE cross-subgoal leak ========"\<close>

ML \<open>
val s_conj = mk_state "QQ (?x::nat) \<and> PP (?x::nat)";
val _ = show "R7 start" s_conj;
val s_conj1 = probe' "R7a SPLIT_CONJS" s_conj "SPLIT_CONJS";
val _ = case s_conj1 of SOME s => (probe' "R7b RULE probe_rule_1 on subgoal 1" s "RULE probe_rule_1"; ())
                      | NONE => ();
\<close>

ML \<open>writeln "======== GROUP 2: splitting ========"\<close>

ML \<open>
probe "S1 SPLIT_CONJS" "QQ (?x::nat) \<and> PP (?x::nat)" "SPLIT_CONJS";
probe "S2 SPLIT_CONJS2" "QQ (?x::nat) \<and> PP (?x::nat)" "SPLIT_CONJS2";
probe "S3 CASE_SPLIT on the schematic itself" "rev (rev (?xs::nat list)) = ?xs" "CASE_SPLIT ?xs";
probe_fix ["ys"] "S4ctl CASE_SPLIT control (no schematic)"
      "rev (rev (ys::nat list)) = ys" "CASE_SPLIT ys";
probe_fix ["ys"] "S4 CASE_SPLIT on free var, ?x elsewhere"
      "rev (rev (ys::nat list)) = ys \<and> QQ (?x::nat)" "CASE_SPLIT ys";
probe "S5 INDUCT on the schematic itself" "rev (rev (?xs::nat list)) = ?xs" "INDUCT ?xs";
probe_fix ["ys"] "S6ctl INDUCT control (no schematic)"
      "rev (rev (ys::nat list)) = ys" "INDUCT ys";
probe_fix ["ys"] "S6 INDUCT on free var, ?x elsewhere"
      "rev (rev (ys::nat list)) = ys \<and> QQ (?x::nat)" "INDUCT ys";
\<close>

ML \<open>
probe_full "S7 CONSIDER (BRANCH)" "QQ (?x::nat)"
      "CONSIDER c1: \"PP (1::nat)\" | c2: \"PP (2::nat)\"";
\<close>

ML \<open>writeln "======== GROUP 4: auto tactics ========"\<close>

ML \<open>probe "A1 SIMPLIFY" "?x + 0 = (?x::nat)" "SIMPLIFY";\<close>
ML \<open>probe "A2 SIMPLIFY on QQ ?x \<and> 0<1" "QQ (?x::nat) \<and> 0 < (1::nat)" "SIMPLIFY";\<close>
ML \<open>probe "A2b SIMPLIFY on ?x = 0" "(?x::nat) = 0" "SIMPLIFY";\<close>
ML \<open>probe "A3 UNFOLD FOO_def" "FOO (?x::nat) = ?x + 1" "UNFOLD FOO_def";\<close>
ML \<open>probe "A4 INTRO" "\<And>y::nat. PP y \<Longrightarrow> QQ (?x::nat)" "INTRO";\<close>
ML \<open>probe "A5 CHOOSE (WITNESS) literal" "\<exists>y::nat. y = ?x" "CHOOSE 0";\<close>
ML \<open>probe "A5b CHOOSE (WITNESS) quoted literal" "\<exists>y::nat. y = ?x" "CHOOSE \"0::nat\"";\<close>
ML \<open>probe "A6 CHOOSE (WITNESS) the schematic" "\<exists>y::nat. y = ?x" "CHOOSE \"?x::nat\"";\<close>

ML \<open>writeln "======== GROUP 6: structured ========"\<close>

ML \<open>probe "C1 HAVE plain" "QQ (?x::nat)" "HAVE h: \"PP (1::nat)\"";\<close>
ML \<open>probe "C2 HAVE with schematic in statement" "QQ (?x::nat)" "HAVE h: \"PP ?y\"";\<close>
ML \<open>probe "C3 SUFFICES" "QQ (?x::nat)" "SUFFICES \"PP (7::nat)\"";\<close>
ML \<open>probe_full "C4 CONSIDER/OBTAIN" "QQ (?x::nat)" "CONSIDER (z::nat) where c: \"PP z\"";\<close>
ML \<open>probe "C5 CHAINING" "QQ (?x::nat)" "CHAINING probe_rule_1";\<close>
ML \<open>probe "C6 SPECIALIZE" "QQ (?x::nat)" "SPECIALIZE sp: probe_rule_2 where n = \"3::nat\"";\<close>
ML \<open>probe "C7 INST_VAR" "QQ (?x::nat)" "INST_VAR ?x = \"7::nat\"";\<close>
ML \<open>probe "C8 STEP (calculation)" "(?x::nat) + 0 = ?x" "STEP \"?x::nat\"";\<close>

ML \<open>writeln "======== GROUP 7: sorry family ========"\<close>

ML \<open>probe "Y1 SORRY_NEXT" "QQ (?x::nat) \<and> PP (?x::nat)" "SPLIT_CONJS SORRY_NEXT";\<close>
ML \<open>probe "Y2 SORRY_END_ALL" "QQ (?x::nat) \<and> PP (?x::nat)" "SPLIT_CONJS SORRY_END_ALL";\<close>
ML \<open>probe "Y3 SORRY_ONLY" "QQ (?x::nat)" "SORRY_ONLY";\<close>
ML \<open>probe_final "Y4 SORRY_END_ALL final thm" "QQ (?x::nat)" "SORRY_END_ALL";\<close>

ML \<open>writeln "======== GROUP 8: misc ========"\<close>

ML \<open>probe "M1 CONTRADICTION (RULE ccontr + INTRO)" "QQ (?x::nat)" "RULE ccontr INTRO";\<close>
ML \<open>probe "M2 DEFINE" "QQ (?x::nat)" "DEFINE gg where \"gg (n::nat) = n + 2\"";\<close>
ML \<open>probe "M3 PRINT (no-op)" "QQ (?x::nat)" "PRINT";\<close>
ML \<open>probe "M4 APPLY (raw tactic)" "QQ (?x::nat)" "APPLY (rule probe_rule_1)";\<close>
ML \<open>probe "M5 COMPUTE" "QQ (?x::nat)" "COMPUTE cc = \"2+3::nat\"";\<close>

ML \<open>writeln "======== GROUP 3: END / NEXT (slow, sledgehammer) ========"\<close>

ML \<open>probe_final "E1 END on provable schematic goal" "?x + 0 = (?x::nat)" "END";\<close>
ML \<open>probe_final "E2 END on bare ?P :: bool" "?P" "END";\<close>
ML \<open>probe_final "E4 END on ?x = 0 (forceable)" "(?x::nat) = 0" "END";\<close>
ML \<open>probe "E3 END on QQ ?x (needs instantiation)" "QQ (?x::nat)" "END";\<close>

ML \<open>
val s_two = mk_state "((?x::nat) + 0 = ?x) \<and> ((?x::nat) * 1 = ?x)";
val s_two1 = probe' "N1a SPLIT_CONJS" s_two "SPLIT_CONJS";
val s_two2 = case s_two1 of SOME s => probe' "N1b NEXT" s "NEXT" | NONE => NONE;
val _ = case s_two2 of SOME s => (probe' "N1c END" s "END"; ()) | NONE => ();
\<close>

ML \<open>writeln "======== GROUP 5: HAMMER ========"\<close>

ML \<open>probe_final "H1 HAMMER on provable schematic goal" "?x + 0 = (?x::nat)" "HAMMER";\<close>
ML \<open>probe_final "H2 HAMMER on ?x = 0" "(?x::nat) = 0" "HAMMER";\<close>

ML \<open>writeln "======== GROUP 9: direct-ML (AoA) paths ========"\<close>

ML \<open>
(* AoA calls these ML entry points directly; their surface syntax either
   does not exist or carries different default flags. *)
fun probe_ml label prop_str fixes (opr : Minilang.operation) =
  case catching label (fn () => opr (mk_state' fixes prop_str))
    of SOME s => show (label ^ "  [OK] goal=" ^ prop_str) s
     | NONE => ()

fun rd fixes str = Syntax.read_term (fix_ctxt fixes base_ctxt) str
\<close>

ML \<open>(* SIMPLIFY as AoA calls it: simplify_goal = true *)
probe_ml "G1 SIMPLIFY(simplify_goal=true) on ?x + 0 = ?x" "?x + 0 = (?x::nat)" []
  (Minilang.SIMPLIFY_GOAL_AND_PREMISES'' [] true [] true);\<close>

ML \<open>probe_ml "G2 SIMPLIFY(simplify_goal=true) on ?x = 0" "(?x::nat) = 0" []
  (Minilang.SIMPLIFY_GOAL_AND_PREMISES'' [] true [] true);\<close>

ML \<open>probe_ml "G3 SIMPLIFY(simplify_goal=true) on QQ ?x \<and> 0<1" "QQ (?x::nat) \<and> 0 < (1::nat)" []
  (Minilang.SIMPLIFY_GOAL_AND_PREMISES'' [] true [] true);\<close>

ML \<open>(* CASE_SPLIT as AoA calls it *)
probe_ml "G4 CASE_SPLIT ys (control, no schematic)" "rev (rev (ys::nat list)) = ys" ["ys"]
  (Minilang.CASE_SPLIT (false, ([[SOME (rd ["ys"] "ys")]], NONE)) NONE []);\<close>

ML \<open>probe_ml "G5 CASE_SPLIT ys, ?x elsewhere"
  "rev (rev (ys::nat list)) = ys \<and> QQ (?x::nat)" ["ys"]
  (Minilang.CASE_SPLIT (false, ([[SOME (rd ["ys"] "ys")]], NONE)) NONE []);\<close>

ML \<open>probe_ml "G6 CASE_SPLIT on a subterm containing ?x" "QQ (?x::nat) \<or> \<not> QQ (?x::nat)" []
  (Minilang.CASE_SPLIT (false, ([[SOME (Syntax.read_term (schematic_ctxt base_ctxt) "QQ (?x::nat)")]], NONE)) NONE []);\<close>

ML \<open>(* INDUCT as AoA calls it *)
probe_ml "G7 INDUCT ys (control, no schematic)" "rev (rev (ys::nat list)) = ys" ["ys"]
  (Minilang.INDUCT (false, ([[SOME (NONE, (rd ["ys"] "ys", false))]], (([[]], []), NONE))) NONE
     {using = [], insertion = []});\<close>

ML \<open>probe_ml "G8 INDUCT ys, ?x elsewhere"
  "rev (rev (ys::nat list)) = ys \<and> QQ (?x::nat)" ["ys"]
  (Minilang.INDUCT (false, ([[SOME (NONE, (rd ["ys"] "ys", false))]], (([[]], []), NONE))) NONE
     {using = [], insertion = []});\<close>

ML \<open>probe_ml "G9 INDUCT on a schematic target" "rev (rev (?xs::nat list)) = ?xs" []
  (Minilang.INDUCT (false, ([[SOME (NONE,
      (Syntax.read_term (schematic_ctxt base_ctxt) "?xs::nat list", false))]], (([[]], []), NONE))) NONE
     {using = [], insertion = []});\<close>

ML \<open>probe_ml "G10 COMPUTE" "QQ (?x::nat)" []
  (Minilang.COMPUTE "cc" (rd [] "2 + 3 :: nat"));\<close>

ML \<open>probe_ml "G11 COMPUTE on a term containing ?x" "QQ (?x::nat)" []
  (Minilang.COMPUTE "cc" (Syntax.read_term (schematic_ctxt base_ctxt) "(?x::nat) + 0"));\<close>

ML \<open>probe "G12 CHAINING (correct syntax)" "QQ (?x::nat)" "CHAINING ch WITH probe_rule_1";\<close>

ML \<open>probe_full "G13 CONSIDER/OBTAIN with vars" "QQ (?x::nat)" "CONSIDER z where c: \"PP z\"";\<close>

ML \<open>probe_full "G14 CONTRADICTION full stack" "QQ (?x::nat)" "RULE ccontr INTRO";\<close>

ML \<open>writeln "======== GROUP 10: what does sledgehammer pin ?x to ========"\<close>

ML \<open>probe_final "H3 HAMMER on ?x < 10 (many solutions)" "(?x::nat) < 10" "HAMMER";\<close>
ML \<open>probe_final "H4 HAMMER on ?x + ?x = 2 * ?x (no inst needed)" "(?x::nat) + ?x = 2 * ?x" "HAMMER";\<close>
ML \<open>probe_final "H5 HAMMER on \<exists>y. y = ?x" "\<exists>y::nat. y = ?x" "HAMMER";\<close>
ML \<open>probe_final "H6 HAMMER on ?x = 3 + 4" "(?x::nat) = 3 + 4" "HAMMER";\<close>

end
