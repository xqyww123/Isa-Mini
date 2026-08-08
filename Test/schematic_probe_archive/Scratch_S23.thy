theory Scratch_S23
  imports Minilang
begin

(* S23 probe: compare the OLD formulation of SORRY_i
     (Tactic.rule_by_tactic ctxt (Skip_Proof.cheat_tac ctxt 1) st)
   against the NEW planned formulation
     (Seq head of Skip_Proof.cheat_tac ctxt 1 st applied directly).
   States are built the way Minilang builds HHF states: Goal.init on a cterm.
   READ-ONLY probe: no edits to proof.ML. *)

ML \<open>
fun old_form ctxt st = Tactic.rule_by_tactic ctxt (Skip_Proof.cheat_tac ctxt 1) st

fun new_form ctxt st =
  case Seq.pull (Skip_Proof.cheat_tac ctxt 1 st) of
    NONE => error "cheat_tac returned empty sequence"
  | SOME (st', _) => st'

fun s_ix (n, i) = n ^ "." ^ string_of_int i

fun vars_of th =
  Term.add_vars (Thm.full_prop_of th) [] |> map (s_ix o fst)
fun tvars_of th =
  Term.add_tvars (Thm.full_prop_of th) [] |> map (s_ix o fst)

fun protected th = can Logic.unprotect (Thm.concl_of th)

fun dump ctxt tag th =
  writeln (tag
    ^ " | nprems=" ^ string_of_int (Thm.nprems_of th)
    ^ " maxidx=" ^ string_of_int (Thm.maxidx_of th)
    ^ " nhyps=" ^ string_of_int (length (Thm.hyps_of th))
    ^ " protected=" ^ (if protected th then "yes" else "no")
    ^ " vars=[" ^ commas (vars_of th) ^ "]"
    ^ " tvars=[" ^ commas (tvars_of th) ^ "]"
    ^ " | prop: " ^ Syntax.string_of_term ctxt (Thm.prop_of th)
    ^ (if null (Thm.hyps_of th) then ""
       else " | hyps: " ^ commas (map (Syntax.string_of_term ctxt) (Thm.hyps_of th))))

fun cmp tag (a, b) =
  writeln (tag
    ^ " | prop_aconv=" ^ Bool.toString (Thm.prop_of a aconv Thm.prop_of b)
    ^ " full_prop_aconv=" ^ Bool.toString (Thm.full_prop_of a aconv Thm.full_prop_of b)
    ^ " hyps_eq=" ^ Bool.toString (eq_list (op aconv) (Thm.hyps_of a, Thm.hyps_of b))
    ^ " shyps_eq=" ^ Bool.toString (eq_set (op =) (Thm.shyps_of a, Thm.shyps_of b))
    ^ " maxidx_eq=" ^ Bool.toString (Thm.maxidx_of a = Thm.maxidx_of b)
    ^ " nprems_eq=" ^ Bool.toString (Thm.nprems_of a = Thm.nprems_of b)
    ^ " protected_eq=" ^ Bool.toString (protected a = protected b))

fun run ctxt tag st =
  let val _ = dump ctxt (tag ^ " STATE") st
      val old_r = SOME (old_form ctxt st)
        handle THM (msg, i, _) =>
          (writeln (tag ^ " OLD raised THM(\"" ^ msg ^ "\", " ^ string_of_int i ^ ")"); NONE)
      val new_r = SOME (new_form ctxt st)
        handle ERROR msg => (writeln (tag ^ " NEW raised ERROR: " ^ msg); NONE)
   in case (old_r, new_r) of
        (SOME a, SOME b) =>
          (dump ctxt (tag ^ " OLD  ") a; dump ctxt (tag ^ " NEW  ") b; cmp (tag ^ " CMP  ") (a, b))
      | _ => ()
  end
\<close>

ML \<open>
val ctxt = @{context}
val nat = @{typ nat}
val bool = @{typ bool}
fun var n i = Var ((n, i), nat)
val zero = @{term "0::nat"}
val one = @{term "1::nat"}
fun eq t u = HOLogic.mk_Trueprop (HOLogic.mk_eq (t, u))
fun init c t = Goal.init (Thm.cterm_of c t)

(* case1: plain, no schematic vars *)
val _ = run ctxt "case1_plain" (init ctxt (eq zero zero))

(* case2: ?x.0 = ?y.9 -- index 0 and NONZERO index in one goal *)
val _ = run ctxt "case2_var0_var9" (init ctxt (eq (var "x" 0) (var "y" 9)))

(* case3: only a nonzero index ?x.9 *)
val _ = run ctxt "case3_var9" (init ctxt (eq (var "x" 9) zero))

(* case4: with a premise, schematic at nonzero index *)
val _ = run ctxt "case4_prem"
  (init ctxt (Logic.mk_implies (eq zero zero, eq (var "x" 3) zero)))

(* case5: meta-quantifier + premise + schematic ?P.5 *)
val a = Free ("a", nat)
val qgoal =
  Logic.all a (Logic.mk_implies (eq a a,
    HOLogic.mk_Trueprop (Var (("P", 5), nat --> bool) $ a)))
val _ = run ctxt "case5_meta_all" (init ctxt qgoal)

(* case6: multiple subgoals (after conjI), vars ?x.0 and ?y.7 *)
val conj_goal = HOLogic.mk_Trueprop (HOLogic.mk_conj
      (HOLogic.mk_eq (var "x" 0, zero), HOLogic.mk_eq (var "y" 7, one)))
val st_multi =
  (case Seq.pull (resolve_tac ctxt @{thms conjI} 1 (init ctxt conj_goal)) of
     SOME (st', _) => st' | NONE => error "conjI failed")
val _ = run ctxt "case6_multi" st_multi

(* case7: SOLVED state (0 subgoals) -- measure the empty-sequence behavior *)
val st_done = new_form ctxt (init ctxt (eq zero zero))
val _ = run ctxt "case7_no_subgoal" st_done

(* case8: context with an assumption -> cheat_tac produces hyps *)
val ([a_name], ctxt1) = Variable.add_fixes ["AA"] ctxt
val Aterm = Free (a_name, bool)
val ([_], ctxt2) =
  Assumption.add_assumes [Thm.cterm_of ctxt1 (HOLogic.mk_Trueprop Aterm)] ctxt1
val _ = run ctxt2 "case8_hyps" (init ctxt2 (eq (var "x" 2) zero))
\<close>

end
