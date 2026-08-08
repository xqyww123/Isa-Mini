theory Scratch_RootMultiGoal
  imports Minilang.Minilang
begin

text \<open>
  Probe for the `Root` gate question: an INITIAL Minilang state with MULTIPLE
  top-level subgoals that SHARE a schematic variable, and what the
  Root sorry-chain + final sequential replay do with it.
\<close>

axiomatization AA :: "nat \<Rightarrow> bool" and BB :: "nat \<Rightarrow> bool" where
  aa7: "AA 7" and bb3: "BB 3" and bb7: "BB 7"

ML \<open>
val base_ctxt = Named_Target.theory_init \<^theory>
fun schematic_ctxt ctxt = Proof_Context.set_mode Proof_Context.mode_schematic ctxt

fun read_prop s = Syntax.read_prop (schematic_ctxt base_ctxt) s

(* Exactly what `by aoa` does: Goal.init on the stated prop, then
   ALLGOALS Goal.conjunction_tac (prepended by Method.CONTEXT_METHOD). *)
fun mk_thm s =
  let val ct = Thm.cterm_of base_ctxt (read_prop s)
      val st = Goal.init ct
   in case SINGLE (ALLGOALS Goal.conjunction_tac) st of
        SOME st' => st'
      | NONE => st
  end

fun mk_state s = Minilang.INIT base_ctxt (mk_thm s)

fun run script s = Minilang.parse_cmds (Minilang.lex_cmds script) s

fun vars_of_each_goal s =
  let val st = Minilang.leading_proof_sequent_of s
      val ctxt = Minilang.context_of s
      val gs = Minilang.goals_of' st
   in cat_lines (map_index (fn (i,g) =>
        "    goal " ^ string_of_int (i+1) ^ " : " ^ Syntax.string_of_term ctxt g
        ^ "   vars=" ^ commas (map (Term.string_of_vname o #1) (Term.add_vars g []))
        ) gs)
  end

fun show label s =
  writeln (label
    ^ "\n    num_goals=" ^ string_of_int (Minilang.num_goals s)
    ^ "   leading_goal_data count=" ^ string_of_int (#2 (Minilang.leading_goal_data s))
    ^ "\n" ^ vars_of_each_goal s)

fun exn_str exn =
  case exn of Minilang.OPR_FAIL (_, m) => "[OPR_FAIL] " ^ m
            | _ => "[EXN] " ^ Runtime.exn_message exn

fun catching label f =
  case Exn.capture f () of
    Exn.Res r => SOME r
  | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn
                   else (writeln (label ^ "  " ^ exn_str exn); NONE)

fun probe' label s0 script =
  case catching label (fn () => run script s0)
    of SOME s => (show (label ^ "  [OK] script=" ^ script) s; SOME s)
     | NONE => NONE
\<close>

section \<open>1. Does INIT accept a multi-subgoal thm at all?\<close>

ML \<open>
val thm_raw = Goal.init (Thm.cterm_of base_ctxt (read_prop "AA ?x &&& BB ?x"));
writeln ("raw Goal.init prems = " ^ string_of_int (length (Thm.prems_of thm_raw)));
val thm2 = mk_thm "AA ?x &&& BB ?x";
writeln ("after conjunction_tac prems = " ^ string_of_int (length (Thm.prems_of thm2)));
val s0 = mk_state "AA ?x &&& BB ?x";
show "S0 (the initial Minilang state, i.e. Root.ml_state)" s0;
\<close>

section \<open>2. Root's sorry-chain: sibling-2 start state\<close>

ML \<open>
val s_child2 = probe' "SORRY_NEXT (derives goal2's start state)" s0 "SORRY_NEXT";
\<close>

section \<open>3. Each child, proved independently against its own start state\<close>

ML \<open>
(* child 1 works on s0: pins ?x := 7 *)
val _ = probe' "child1 on s0: RULE aa7" s0 "RULE aa7";
(* child 2 works on the sorry-derived state: pins ?x := 3 *)
val _ = case s_child2 of SOME s => (probe' "child2 on sorry-state: RULE bb3" s "RULE bb3"; ())
                       | NONE => ();
\<close>

section \<open>4. The final sequential replay of the assembled op list\<close>

ML \<open>
writeln "---- conflicting assembly: RULE aa7 NEXT RULE bb3 END ----";
val _ = probe' "ASSEMBLY conflicting" s0 "RULE aa7 NEXT RULE bb3";
writeln "---- consistent assembly: RULE aa7 NEXT RULE bb7 END ----";
val _ = probe' "ASSEMBLY consistent" s0 "RULE aa7 NEXT RULE bb7";
\<close>

section \<open>5. Do the two top-level goals really share the same Var?\<close>

ML \<open>
val s_indep = mk_state "AA ?x &&& BB ?y";
show "S0' independent schematics (AA ?x &&& BB ?y)" s_indep;
val _ = probe' "ASSEMBLY independent" s_indep "RULE aa7 NEXT RULE bb3";
\<close>

section \<open>6. The realistic producers of a multi-subgoal initial state\<close>

ML \<open>
(* (a) `apply (rule conjI)` then `apply aoa`: the plainest case. *)
val bc = Named_Target.theory_init \<^theory>
fun rp s = Syntax.read_prop (Proof_Context.set_mode Proof_Context.mode_schematic bc) s
val st_conj = Goal.init (Thm.cterm_of bc (rp "AA ?x \<and> BB ?x"))
val st_conj2 = the (SINGLE (resolve_tac bc @{thms conjI} 1) st_conj)
val s_conj = Minilang.INIT bc st_conj2
val _ = show "P1 after `rule conjI`" s_conj
val _ = probe' "P1 assembly conflicting" s_conj "RULE aa7 NEXT RULE bb3"
\<close>

text \<open>(b) `Goal_Preprocess.custom_split_tac` (Agent/preprocess.ML) lives in the
  Minilang_AoA session, not in Minilang, so it cannot be probed from here.  Its
  conjunction case is literally a resolve_tac with conjI -- i.e.
  exactly case (a) above, applied recursively.\<close>

end
