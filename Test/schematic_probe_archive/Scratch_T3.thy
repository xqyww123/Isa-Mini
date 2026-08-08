theory Scratch_T3
  imports Minilang.Minilang
begin

(* T3 probe: does the explicit Intro operation (AUTO_INTRO -> INTRO' ->
   Subgoal.focus_prems ... Subgoal.retrofit) drift the indexnames of
   schematic variables?  MEASURE ONLY. *)

axiomatization PP :: "nat \<Rightarrow> bool" and QQ :: "nat \<Rightarrow> bool"

ML \<open>
(* ---- harness (adapted from Scratch_SchematicProbe.thy; mk_state' fixed:
       Variable.declare_term the goal so fixed frees keep their types) ---- *)

val base_ctxt = Named_Target.theory_init \<^theory>

fun fix_ctxt fixes ctxt = #2 (Variable.add_fixes fixes ctxt)

fun schematic_ctxt ctxt = Proof_Context.set_mode Proof_Context.mode_schematic ctxt

fun mk_state' fixes prop_str =
  let val ctxt0 = fix_ctxt fixes base_ctxt
      val t = Syntax.read_prop (schematic_ctxt ctxt0) prop_str
      val ctxt = Variable.declare_term t ctxt0
      val ct = Thm.cterm_of ctxt t
   in Minilang.INIT ctxt (Goal.init ct) end

fun mk_state prop_str = mk_state' [] prop_str

fun run script s = Minilang.parse_cmds (Minilang.lex_cmds script) s

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

(* ---- raw structural dumps -------------------------------------------- *)

(* Applied occurrences of Vars: (indexname, number of arguments). *)
fun var_occs tm acc =
  case Term.strip_comb tm of
    (Var (xi, _), args) =>
      fold var_occs args (insert (op =) (xi, length args) acc)
  | (Abs (_, _, b), args) => fold var_occs args (var_occs b acc)
  | (_, args) => fold var_occs args acc

fun dump_term ctxt tag t =
  let
    val vars = rev (Term.add_vars t [])
    val frees = rev (Term.add_frees t [])
    val tvars = rev (Term.add_tvars t [])
    val occs = rev (var_occs t [])
    (* NB: internal type-variable names carry the leading apostrophe. *)
    fun tvline ((n, i), S) =
      "    TVar (\"" ^ n ^ "\", " ^ string_of_int i ^ ")  disp=" ^
      Term.string_of_vname (n, i) ^ "  :: " ^ commas S
    fun vline ((n, i), T) =
      "    Var (\"" ^ n ^ "\", " ^ string_of_int i ^ ")  disp=" ^
      Term.string_of_vname (n, i) ^ "  :: " ^ Syntax.string_of_typ ctxt T
    fun fline (n, T) =
      "    Free \"" ^ n ^ "\"  :: " ^ Syntax.string_of_typ ctxt T
    fun oline ((n, i), k) =
      "    " ^ Term.string_of_vname (n, i) ^ " applied to " ^
      string_of_int k ^ " args"
  in
    writeln (tag ^ "\n  term: " ^ Syntax.string_of_term ctxt t ^
             "\n  Vars:\n" ^ cat_lines (map vline vars) ^
             "\n  TVars:\n" ^ cat_lines (map tvline tvars) ^
             "\n  Frees:\n" ^ cat_lines (map fline frees) ^
             "\n  Var occurrences:\n" ^ cat_lines (map oline occs))
  end

fun dump label s =
  let val ctxt = Minilang.context_of s
      val st = Minilang.leading_proof_sequent_of s
  in dump_term ctxt ("==== " ^ label ^ " ====") (Thm.prop_of st) end

fun dump_goals label s =
  let val ctxt = Minilang.context_of s
      val st = Minilang.leading_proof_sequent_of s
      val gs = Minilang.goals_of' st
  in writeln ("==== " ^ label ^ " ====  (" ^ string_of_int (length gs) ^ " subgoals)");
     List.app (fn (i, g) => dump_term ctxt ("  -- subgoal " ^ string_of_int (i+1)) g)
              (map_index I gs)
  end

(* The AoA explicit-Intro path: AUTO_INTRO's step 5 is exactly
   Minilang.INTRO SINGLE_GOAL NONE var_names prem_names. *)
fun do_intro var_names prem_names s =
  let val ((params', facts'), s') =
        Minilang.INTRO Minilang.SINGLE_GOAL NONE var_names prem_names s
      val ctxt' = Minilang.context_of s'
      val _ = writeln ("  INTRO params: " ^
                commas (map (fn (n, T) => n ^ " :: " ^ Syntax.string_of_typ ctxt' T) params'))
      val _ = writeln ("  INTRO facts: " ^
                commas (map (fn (n, t) => n ^ ": " ^ Syntax.string_of_term ctxt' t) facts'))
   in s' end
\<close>

ML \<open>writeln "######## CASE A: single subgoal, block closed by using a premise ########"\<close>

ML \<open>
val sA0 = mk_state "\<And>y::nat. PP ?x \<Longrightarrow> QQ ?x9 \<Longrightarrow> QQ ?x9";
val _ = dump "A before Intro" sA0;
val sA1 = do_intro (SOME [SOME "y"]) (SOME [SOME "h1", SOME "h2"]) sA0;
val _ = dump "A inside block (after Intro)" sA1;
val sA2 = catching "A close block by APPLY (rule h2)" (fn () => run "APPLY (rule h2)" sA1);
val _ = case sA2 of SOME s => dump "A after block closes" s | NONE => ();
val _ = case sA2 of
          SOME s =>
            (case catching "A conclude" (fn () => Minilang.conclude base_ctxt s) of
               SOME th => dump_term base_ctxt "==== A final theorem ====" (Thm.prop_of th)
             | NONE => ())
        | NONE => ();
\<close>

ML \<open>writeln "######## CASE B: shared vars across 2 subgoals; inner proof does NOT touch frozen vars ########"\<close>

ML \<open>
val sB0 = mk_state
  "(\<forall>y::nat. PP ?x \<longrightarrow> QQ ?x9 \<longrightarrow> y = y) \<and> (PP ?x \<or> QQ ?x9 \<or> QQ ?z2)";
val _ = dump "B start" sB0;
val sB1 = catching "B SPLIT_CONJS" (fn () => run "SPLIT_CONJS" sB0);
val _ = case sB1 of SOME s => (dump "B after SPLIT_CONJS" s; dump_goals "B subgoals" s) | NONE => ();
\<close>

ML \<open>
val sB2 = case sB1 of
    SOME s => catching "B Intro on subgoal 1"
                (fn () => do_intro (SOME [SOME "y"]) (SOME [SOME "h1", SOME "h2"]) s)
  | NONE => NONE;
val _ = case sB2 of SOME s => dump "B inside block (after Intro)" s | NONE => ();
val sB3 = case sB2 of
    SOME s => catching "B close block by APPLY (rule refl) NEXT" (fn () => run "APPLY (rule refl) NEXT" s)
  | NONE => NONE;
val _ = case sB3 of SOME s => (dump "B after block closes" s; dump_goals "B remaining subgoals" s) | NONE => ();
\<close>

ML \<open>writeln "######## CASE B chain: instantiate by the PRE-Intro indexname ########"\<close>

ML \<open>
(* The practically-relevant chain: the LLM recorded ?x / ?x9 / ?z2 BEFORE
   Intro; after the block closes it instantiates by those names. *)
val _ = case sB3 of
    SOME s =>
      (case catching "B INST_VAR ?x9 = 7" (fn () => run "INST_VAR ?x9 = \"7::nat\"" s) of
         SOME s' => dump "B after INST_VAR ?x9 = 7" s'
       | NONE => ())
  | NONE => ();
val _ = case sB3 of
    SOME s =>
      (case catching "B INST_VAR ?x = 5" (fn () => run "INST_VAR ?x = \"5::nat\"" s) of
         SOME s' => dump "B after INST_VAR ?x = 5" s'
       | NONE => ())
  | NONE => ();
val _ = case sB3 of
    SOME s =>
      (case catching "B INST_VAR ?z2 = 3" (fn () => run "INST_VAR ?z2 = \"3::nat\"" s) of
         SOME s' => dump "B after INST_VAR ?z2 = 3" s'
       | NONE => ())
  | NONE => ();
\<close>

ML \<open>writeln "######## CASE C: shared vars, inner proof DOES use a frozen premise ########"\<close>

ML \<open>
val sC0 = mk_state
  "(\<forall>y::nat. PP ?x \<longrightarrow> QQ ?x9 \<longrightarrow> QQ ?x9) \<and> (PP ?x \<or> QQ ?x9 \<or> QQ ?z2)";
val _ = dump "C start" sC0;
val sC1 = catching "C SPLIT_CONJS" (fn () => run "SPLIT_CONJS" sC0);
val sC2 = case sC1 of
    SOME s => catching "C Intro on subgoal 1"
                (fn () => do_intro (SOME [SOME "y"]) (SOME [SOME "h1", SOME "h2"]) s)
  | NONE => NONE;
val _ = case sC2 of SOME s => dump "C inside block (after Intro)" s | NONE => ();
val sC3 = case sC2 of
    SOME s => catching "C close block by APPLY (rule h2) NEXT" (fn () => run "APPLY (rule h2) NEXT" s)
  | NONE => NONE;
val _ = case sC3 of SOME s => (dump "C after block closes" s; dump_goals "C remaining subgoals" s) | NONE => ();
val _ = case sC3 of
    SOME s =>
      (case catching "C INST_VAR ?x9 = 7" (fn () => run "INST_VAR ?x9 = \"7::nat\"" s) of
         SOME s' => dump "C after INST_VAR ?x9 = 7" s'
       | NONE => ())
  | NONE => ();
\<close>

ML \<open>writeln "######## CASE D: applied schematic ?f y across the block ########"\<close>

ML \<open>
val sD0 = mk_state
  "(\<forall>y::nat. PP (?f y) \<longrightarrow> PP (?f y)) \<and> PP (?f (0::nat))";
val _ = dump "D start" sD0;
val sD1 = catching "D SPLIT_CONJS" (fn () => run "SPLIT_CONJS" sD0);
val sD2 = case sD1 of
    SOME s => catching "D Intro on subgoal 1"
                (fn () => do_intro (SOME [SOME "y"]) (SOME [SOME "h1"]) s)
  | NONE => NONE;
val _ = case sD2 of SOME s => dump "D inside block (after Intro)" s | NONE => ();
val sD3 = case sD2 of
    SOME s => catching "D close block by APPLY (rule h1) NEXT" (fn () => run "APPLY (rule h1) NEXT" s)
  | NONE => NONE;
val _ = case sD3 of SOME s => (dump "D after block closes" s; dump_goals "D remaining subgoals" s) | NONE => ();
val _ = case sD3 of
    SOME s =>
      (case catching "D INST_VAR ?f = (%n. n)" (fn () => run "INST_VAR ?f = \"\<lambda>n::nat. n\"" s) of
         SOME s' => dump "D after INST_VAR ?f" s'
       | NONE => ())
  | NONE => ();
\<close>

ML \<open>writeln "######## CASE E: param named x collides with base names of ?x / ?x9 ########"\<close>

ML \<open>
val sE0 = mk_state
  "(\<forall>x::nat. PP ?x \<longrightarrow> QQ ?x9 \<longrightarrow> x = x) \<and> (PP ?x \<or> QQ ?x9)";
val _ = dump "E start" sE0;
val sE1 = catching "E SPLIT_CONJS" (fn () => run "SPLIT_CONJS" sE0);
val sE2 = case sE1 of
    SOME s => catching "E Intro on subgoal 1, param forced to name x"
                (fn () => do_intro (SOME [SOME "x"]) (SOME [SOME "h1", SOME "h2"]) s)
  | NONE => NONE;
val _ = case sE2 of SOME s => dump "E inside block (after Intro)" s | NONE => ();
val sE3 = case sE2 of
    SOME s => catching "E close block by APPLY (rule refl) NEXT" (fn () => run "APPLY (rule refl) NEXT" s)
  | NONE => NONE;
val _ = case sE3 of SOME s => (dump "E after block closes" s; dump_goals "E remaining subgoals" s) | NONE => ();
val _ = case sE3 of
    SOME s =>
      (case catching "E INST_VAR ?x9 = 7" (fn () => run "INST_VAR ?x9 = \"7::nat\"" s) of
         SOME s' => dump "E after INST_VAR ?x9 = 7" s'
       | NONE => ())
  | NONE => ();
\<close>

ML \<open>writeln "######## CASE F: schematic TYPE variable ?'b2 in the OTHER subgoal ########"\<close>

ML \<open>
(* Variable.importT at focus freezes every TVar of the WHOLE state, not just
   the focused subgoal.  Does ?'b2 (and the term var ?w :: ?'b2) survive? *)
val sF0 = mk_state
  "(\<forall>y::nat. PP ?x \<longrightarrow> y = y) \<and> ((?w::?'b2) = ?w \<or> QQ ?x9)";
val _ = dump "F start" sF0;
val sF1 = catching "F SPLIT_CONJS" (fn () => run "SPLIT_CONJS" sF0);
val sF2 = case sF1 of
    SOME s => catching "F Intro on subgoal 1"
                (fn () => do_intro (SOME [SOME "y"]) (SOME [SOME "h1"]) s)
  | NONE => NONE;
val _ = case sF2 of SOME s => dump "F inside block (after Intro)" s | NONE => ();
val sF3 = case sF2 of
    SOME s => catching "F close block by APPLY (rule refl) NEXT" (fn () => run "APPLY (rule refl) NEXT" s)
  | NONE => NONE;
val _ = case sF3 of SOME s => (dump "F after block closes" s; dump_goals "F remaining subgoals" s) | NONE => ();
val _ = case sF3 of
    SOME s =>
      (case catching "F INST_VAR ?w = 7 (forces ?'b2 := nat)"
              (fn () => run "INST_VAR ?w = \"7::nat\"" s) of
         SOME s' => dump "F after INST_VAR ?w = 7" s'
       | NONE => ())
  | NONE => ();
\<close>

ML \<open>
(* Control: the same INST_VAR type-conflict WITHOUT any Intro block, to show
   the failure is a property of INST_VAR itself, not of the retrofit. *)
val _ = case sF1 of
    SOME s =>
      (case catching "F-control INST_VAR ?w = 7 on the pre-Intro state"
              (fn () => run "INST_VAR ?w = \"7::nat\"" s) of
         SOME s' => dump "F-control after INST_VAR ?w = 7 (no Intro ever ran)" s'
       | NONE => ())
  | NONE => ();
\<close>

end
