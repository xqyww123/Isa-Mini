theory Scratch_M9
  imports Minilang.Minilang
begin

(* M9 probe: verify the shared-schematic top-level-subgoal merge construction
   (replica of the AoA_RPC head block in Agent/agent_server.ML).
   Multi-subgoal states are built the way `lemma "A" "B"` builds them:
   Goal.init on the Pure conjunction, then Goal.conjunction_tac.
   D1: 2 subgoals sharing ?x -> merged into one conj subgoal; proving it
       instantiates ?x and Goal.conclude returns the ORIGINAL conclusion.
   D2: 2 subgoals with disjoint vars -> untouched.
   D3: single subgoal -> untouched.
   D4: meta-structured subgoal (!!y. PP y ==> SS ?x) atomizes then merges.
   D5: shared TVar triggers the merge too. *)

axiomatization SS :: "nat \<Rightarrow> bool" and TT :: "nat \<Rightarrow> bool"
           and PP :: "nat \<Rightarrow> bool"
  where ss7: "SS 7" and tt7: "TT 7" and pp_any: "PP y"

ML \<open>
val ctxt0 = Named_Target.theory_init \<^theory>
val schematic_ctxt = Proof_Context.set_mode Proof_Context.mode_schematic

(* Multi-subgoal state: Goal.init (G1 &&& ... &&& Gn), split by conjunction_tac. *)
fun mk_state goal_strs =
  let val ctxt1 = schematic_ctxt ctxt0
      val gs = map (Syntax.read_prop ctxt1) goal_strs
      val ctxt2 = fold Variable.declare_term gs ctxt0
      val goal = foldr1 Logic.mk_conjunction gs
      val st = Goal.init (Thm.cterm_of ctxt2 goal)
   in if length gs = 1 then st
      else case Seq.pull (Goal.conjunction_tac 1 st) of
             SOME (st', _) => st'
           | NONE => raise Fail "mk_state: conjunction_tac failed"
  end

(* --- replica of the M9 merge block (agent_server.ML, AoA_RPC head) --- *)
fun merge_shared ctxt0 sequent =
  let val prems = Thm.prems_of sequent
      fun shares (t1, t2) =
        exists (member (op =) (Term.add_vars t2 [])) (Term.add_vars t1 [])
        orelse exists (member (op =) (Term.add_tvars t2 [])) (Term.add_tvars t1 [])
      fun any_shared [] = false
        | any_shared (t :: ts) =
            exists (fn t' => shares (t, t')) ts orelse any_shared ts
  in if length prems < 2 orelse not (any_shared prems) then sequent
     else let
       fun give_up () = raise Fail "M9 give-up: atomize failed"
       val atomized =
         case Seq.pull (ALLGOALS (Object_Logic.full_atomize_tac ctxt0) sequent) of
           SOME (st, _) => st
         | NONE => give_up ()
       val ((_, [atomized']), ctxt') = Variable.import true [atomized] ctxt0
       val props = map (fn t => HOLogic.dest_Trueprop t
                                handle TERM _ => give_up ())
                       (Thm.prems_of atomized')
       val conj_ct = Thm.cterm_of ctxt'
                       (HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj props))
       val cj = Thm.assume conj_ct
       fun conjuncts 1 th = [th]
         | conjuncts k th =
             (th RS @{thm conjunct1}) :: conjuncts (k - 1) (th RS @{thm conjunct2})
       val merged' =
         fold (fn th => fn st => Thm.implies_elim st th)
              (conjuncts (length props) cj) atomized'
         |> Thm.implies_intr conj_ct
    in case Variable.export ctxt' ctxt0 [merged'] of
         [th] => th
       | _ => give_up ()
    end
  end

fun report tag st =
  writeln (tag ^ ": " ^ Int.toString (Thm.nprems_of st) ^ " subgoal(s) | " ^
           Syntax.string_of_term ctxt0 (Thm.prop_of st))

(* ---------- D1: shared ?x, 2 subgoals ---------- *)
val st0 = mk_state ["SS (?x::nat)", "TT (?x::nat)"]
val _ = report "D1 before" st0
val _ = if Thm.nprems_of st0 = 2 then () else raise Fail "D1: harness broken"
val st1 = merge_shared ctxt0 st0
val _ = report "D1 merged" st1
val _ = if Thm.nprems_of st1 = 1 then () else raise Fail "D1: expected 1 subgoal"
val proved =
  case Seq.pull ((resolve_tac ctxt0 @{thms conjI} 1
                  THEN resolve_tac ctxt0 @{thms ss7} 1
                  THEN resolve_tac ctxt0 @{thms tt7} 1) st1) of
    SOME (st, _) => st
  | NONE => raise Fail "D1: proof of merged goal failed"
val final = Goal.conclude proved
val _ = writeln ("D1 final: " ^ Syntax.string_of_term ctxt0 (Thm.prop_of final))
val expected = Logic.mk_conjunction (\<^prop>\<open>SS 7\<close>, \<^prop>\<open>TT 7\<close>)
val _ = if Thm.prop_of final aconv expected
        then writeln "D1 PASS" else raise Fail "D1: wrong final theorem"
val _ = if null (Thm.hyps_of final) then () else raise Fail "D1: hyps leaked"

(* ---------- D2: disjoint vars -> untouched ---------- *)
val st0 = mk_state ["SS (?x::nat)", "TT (?y::nat)"]
val st1 = merge_shared ctxt0 st0
val _ = if Thm.eq_thm_prop (st0, st1) then writeln "D2 PASS (untouched)"
        else raise Fail "D2: state changed"

(* ---------- D3: single subgoal -> untouched ---------- *)
val st0 = mk_state ["SS (?x::nat)"]
val st1 = merge_shared ctxt0 st0
val _ = if Thm.eq_thm_prop (st0, st1) then writeln "D3 PASS (untouched)"
        else raise Fail "D3: state changed"

(* ---------- D4: meta-structure atomizes then merges ---------- *)
val st0 = mk_state ["\<And>y. PP y \<Longrightarrow> SS (?x::nat)", "TT (?x::nat)"]
val _ = report "D4 before" st0
val st1 = merge_shared ctxt0 st0
val _ = report "D4 merged" st1
val _ = if Thm.nprems_of st1 = 1 then writeln "D4 PASS"
        else raise Fail "D4: expected 1 subgoal"

(* ---------- D5: shared TVar triggers merge ---------- *)
val st0 = mk_state ["(?a::?'t) = ?a", "(?b::?'t) = ?b"]
val _ = report "D5 before" st0
val st1 = merge_shared ctxt0 st0
val _ = report "D5 merged" st1
val _ = if Thm.nprems_of st1 = 1 then writeln "D5 PASS"
        else raise Fail "D5: expected 1 subgoal"
\<close>

end
