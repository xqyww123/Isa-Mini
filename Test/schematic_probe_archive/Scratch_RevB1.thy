theory Scratch_RevB1
  imports Minilang.Minilang
begin

(* ROUND-1 review probe (READ-ONLY, no edits to proof.ML):
   measure the CURRENT, reworked SUFFICES' (commit 75a65a7: full_atomize
   objectification) on goals that PASS the kept schematic-vars guard, to
   test whether S22's old-path evidence transfers to the new path.

   B1: schematic ?x in a META PREMISE, clean conclusion -> passes the guard
       TODAY, but the objectification folds ?x into the obligation, a shape
       the old code never built. Full life cycle: open, prove obligation
       without pinning ?x, close, solve residual goal, conclude.
   B2: schematic ?x in the conclusion -> the guard must still fire.
   B3: goal with a \<And>-binder -> old path crashed (loose Bound, plan 4.10);
       new path should atomize and open. Baseline change vs S22 regression. *)

axiomatization PP :: "nat \<Rightarrow> bool" and QQ :: "nat \<Rightarrow> bool"
           and RR :: "nat \<Rightarrow> bool" where
  probe_rule_2: "PP n \<Longrightarrow> QQ n" and
  rr3: "RR 3"

ML \<open>
val base_ctxt = Named_Target.theory_init \<^theory>

fun schematic_ctxt ctxt = Proof_Context.set_mode Proof_Context.mode_schematic ctxt

fun mk_state prop_str =
  let val ctxt = base_ctxt
      val t  = Syntax.read_prop (schematic_ctxt ctxt) prop_str
      val ct = Thm.cterm_of ctxt t
   in Minilang.INIT ctxt (Goal.init ct) end

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

fun probe label prop_str script =
  case catching label (fn () => run script (mk_state prop_str))
    of SOME s => show (label ^ "  [OK] goal=" ^ prop_str ^ "  script=" ^ script) s
     | NONE => ()

fun probe_final label prop_str script =
  case catching label (fn () => run script (mk_state prop_str))
    of SOME s =>
        (show (label ^ "  [OK] goal=" ^ prop_str ^ "  script=" ^ script) s;
         case catching (label ^ " conclude") (fn () => Minilang.conclude base_ctxt s)
           of SOME th =>
                writeln ("  RESULT THM: " ^
                    Syntax.string_of_term base_ctxt (Thm.prop_of th) ^
                    "\n  RESULT hyps=" ^ string_of_int (length (Thm.hyps_of th)) ^
                    " tpairs=" ^ string_of_int (length (Thm.tpairs_of th)))
            | NONE => ())
     | NONE => ()
\<close>

ML \<open>writeln "======== RevB1 GROUP B1: premise-schematic through the objectified path ========"\<close>

ML \<open>
(* Open only: watch the reported obligation shape. *)
probe "B1a SUFFICES open (premise ?x)" "PP ?x \<Longrightarrow> RR 3" "SUFFICES \"RR (3::nat)\"";
\<close>

ML \<open>
(* Full life cycle: obligation proved WITHOUT pinning ?x (intro impI +
   assumption is deterministic), block closed, residual goal RR 3 solved
   by rr3, then conclude. Expected good outcome: RESULT THM = PP ?x ==> RR 3
   with ?x alive, hyps=0, tpairs=0. Any deviation is a finding. *)
probe_final "B1b SUFFICES full cycle (premise ?x)" "PP ?x \<Longrightarrow> RR 3"
  "SUFFICES \"RR (3::nat)\" APPLY (intro impI) APPLY (assumption) END APPLY (rule rr3) END";
\<close>

ML \<open>writeln "======== RevB1 GROUP B2: guard still fires on conclusion-schematic ========"\<close>

ML \<open>
probe "B2 SUFFICES reject (conclusion ?x)" "QQ (?x::nat)" "SUFFICES \"PP (7::nat)\"";
\<close>

ML \<open>writeln "======== RevB1 GROUP B3: meta-binder goal now atomizes (old path crashed) ========"\<close>

ML \<open>
probe "B3 SUFFICES open under \<And>-binder" "\<And>y. PP y \<Longrightarrow> PP y" "SUFFICES \"True\"";
\<close>

end
