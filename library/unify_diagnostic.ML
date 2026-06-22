(*  Title:      Isa-Mini/library/unify_diagnostic.ML

Diagnostic variant of Pattern.unify (from Pure/pattern.ML).
Instead of tracing + raise Unif, raises Unif_Diagnostic carrying
structured information about WHY unification failed.

Used by SPECIALIZE to produce actionable error messages for the agent.
*)

signature UNIFY_DIAGNOSTIC =
sig
  datatype unify_diagnostic =
      Type_Clash of typ * typ
    | Clash of string * string
    | BoundVar_Clash of int * int
    | Projection_Fail of indexname * int list * term
    | Occurs_Check of indexname * term

  exception Unif_Diagnostic of unify_diagnostic

  val diagnostic_unify : Context.generic -> term * term -> Envir.env -> Envir.env

  val format_diag_body : Proof.context -> unify_diagnostic -> string
  val diagnose_pair : Proof.context -> term -> term -> unify_diagnostic option
  val diagnose_of_failure : Proof.context -> thm -> thm list -> string option
  val diagnose_rule_vs_goal : Proof.context -> (bool * thm) list -> term -> string option
end

structure Unify_Diagnostic : UNIFY_DIAGNOSTIC =
struct

(* ---- Diagnostic datatype and exception ---- *)

datatype unify_diagnostic =
    Type_Clash of typ * typ
  | Clash of string * string
  | BoundVar_Clash of int * int
  | Projection_Fail of indexname * int list * term
  | Occurs_Check of indexname * term

exception Unif_Diagnostic of unify_diagnostic



(* ---- Diagnostic functions (replace Pattern's tracing versions) ---- *)

fun bname binders i = fst (nth binders i)

fun typ_clash _ (tyenv, T, U) =
  raise Unif_Diagnostic (Type_Clash (
    Envir.norm_type tyenv T,
    Envir.norm_type tyenv U))

fun clash _ a b =
  raise Unif_Diagnostic (Clash (a, b))

fun clashBB _ _ i j =
  raise Unif_Diagnostic (BoundVar_Clash (i, j))

fun clashB _ binders i s =
  raise Unif_Diagnostic (Clash (bname binders i, s))

fun proj_fail _ (_, _, F, _, is, t) =
  raise Unif_Diagnostic (Projection_Fail (F, is, t))

fun ocheck_fail _ (F, t, _, _) =
  raise Unif_Diagnostic (Occurs_Check (F, t))


(* ---- Helpers copied verbatim from pattern.ML ---- *)

fun occurs (F, t, env) =
  let fun occ (Var (G, T)) = (case Envir.lookup env (G, T) of
                                SOME t => occ t
                              | NONE   => F = G)
        | occ (t1 $ t2)     = occ t1 orelse occ t2
        | occ (Abs (_, _, t)) = occ t
        | occ _              = false
  in occ t end

fun mapbnd f =
  let fun mpb d (Bound i)      = if i < d then Bound i else Bound (f (i - d) + d)
        | mpb d (Abs (s, T, t)) = Abs (s, T, mpb (d + 1) t)
        | mpb d (u1 $ u2)      = mpb d u1 $ mpb d u2
        | mpb _ atom            = atom
  in mpb 0 end

fun idx [] j      = raise Unif_Diagnostic (Projection_Fail (("?", 0), [j], Bound j))
  | idx (i :: is) j = if (i : int) = j then length is else idx is j

fun mkabs (binders, is, t) =
  let fun mk (i :: is) = let val (x, T) = nth binders i in Abs (x, T, mk is) end
        | mk []        = t
  in mk is end

val incr = mapbnd (fn i => i + 1)

fun ints_of []              = []
  | ints_of (Bound i :: bs) =
      let val is = ints_of bs
      in if member (op =) is i then raise Pattern.Pattern else i :: is end
  | ints_of _               = raise Pattern.Pattern

fun ints_of' env ts = ints_of (map (Envir.head_norm env) ts)

fun app (s, i :: is) = app (s $ Bound i, is)
  | app (s, [])      = s

fun red (Abs (_, _, s)) (i :: is) js = red s is (i :: js)
  | red t              []         [] = t
  | red t              is         jn = app (mapbnd (nth jn) t, is)

fun split_type (T, 0, Ts)                     = (Ts, T)
  | split_type (Type ("fun", [T1, T2]), n, Ts) = split_type (T2, n - 1, T1 :: Ts)
  | split_type _                               = raise Fail "split_type"

fun type_of_G env (T, n, is) =
  let
    val tyenv = Envir.type_env env
    val (Ts, U) = split_type (Envir.norm_type tyenv T, n, [])
  in map (nth Ts) is ---> U end

fun mk_hnf (binders, is, G, js) = mkabs (binders, is, app (G, js))

fun mk_new_hnf (env, binders, is, F as (a, _), T, js) =
  let val (env', G) = Envir.genvar a (env, type_of_G env (T, length is, js))
  in Envir.update ((F, T), mk_hnf (binders, is, G, js)) env' end

fun downto0 (i :: is, n) = i = n andalso downto0 (is, n - 1)
  | downto0 ([], n)      = n = ~1

fun mk_proj_list is =
  let fun mk (i :: is, j) = if is_some i then j :: mk (is, j - 1) else mk (is, j - 1)
        | mk ([], _)      = []
  in mk (is, length is - 1) end

fun proj (s, env, binders, is) =
  let
    fun trans d i = if i < d then i else idx is (i - d) + d
    fun pr (s, env, d, binders) =
      (case Envir.head_norm env s of
        Abs (a, T, t) =>
          let val (t', env') = pr (t, env, d + 1, (a, T) :: binders)
          in (Abs (a, T, t'), env') end
      | t =>
        (case strip_comb t of
          (c as Const _, ts) =>
            let val (ts', env') = prs (ts, env, d, binders)
            in (list_comb (c, ts'), env') end
        | (f as Free _, ts) =>
            let val (ts', env') = prs (ts, env, d, binders)
            in (list_comb (f, ts'), env') end
        | (Bound i, ts) =>
            let val j = trans d i
                val (ts', env') = prs (ts, env, d, binders)
            in (list_comb (Bound j, ts'), env') end
        | (Var (F as (a, _), Fty), ts) =>
            let val js = ints_of' env ts
                val js' = map (try (trans d)) js
                val ks = mk_proj_list js'
                val ls = map_filter I js'
                val Hty = type_of_G env (Fty, length js, ks)
                val (env', H) = Envir.genvar a (env, Hty)
                val env'' = Envir.update ((F, Fty), mk_hnf (binders, js, H, ks)) env'
            in (app (H, ls), env'') end
        | _ => raise Pattern.Pattern))
    and prs (s :: ss, env, d, binders) =
          let val (s', env1) = pr (s, env, d, binders)
              val (ss', env2) = prs (ss, env1, d, binders)
          in (s' :: ss', env2) end
      | prs ([], env, _, _) = ([], env)
  in
    if downto0 (is, length binders - 1) then (s, env)
    else pr (s, env, 0, binders)
  end

fun mk_ff_list (is, js) =
  let fun mk ([], [], _)         = []
        | mk (i :: is, j :: js, k) = if (i : int) = j then k :: mk (is, js, k - 1)
                                     else mk (is, js, k - 1)
        | mk _                    = raise Fail "mk_ff_list"
  in mk (is, js, length is - 1) end

fun flexflex1 (env, binders, F, Fty, is, js) =
  if is = js then env
  else let val ks = mk_ff_list (is, js)
       in mk_new_hnf (env, binders, is, F, Fty, ks) end

fun flexflex2 (env, binders, F, Fty, is, G, Gty, js) =
  let fun ff (F, Fty, is, G as (a, _), Gty, js) =
        if subset (op =) (js, is)
        then let val t = mkabs (binders, is, app (Var (G, Gty), map (idx is) js))
             in Envir.update ((F, Fty), t) env end
        else let val ks = inter (op =) js is
                 val Hty = type_of_G env (Fty, length is, map (idx is) ks)
                 val (env', H) = Envir.genvar a (env, Hty)
                 fun lam is = mkabs (binders, is, app (H, map (idx is) ks))
             in Envir.update ((G, Gty), lam js) (Envir.update ((F, Fty), lam is) env') end
  in if Term_Ord.indexname_ord (G, F) = LESS
     then ff (F, Fty, is, G, Gty, js)
     else ff (G, Gty, js, F, Fty, is)
  end


(* ---- Core unification (modified from pattern.ML) ---- *)

fun unify_types context (T, U) (env as Envir.Envir {maxidx, tenv, tyenv}) =
  if T = U then env
  else
    let
      val thy = Context.theory_of context
      val (tyenv', maxidx') = Sign.typ_unify thy (U, T) (tyenv, maxidx)
    in Envir.Envir {maxidx = maxidx', tenv = tenv, tyenv = tyenv'} end
    handle Type.TUNIFY => typ_clash context (tyenv, T, U)

fun unif context binders (s, t) env =
  case (Envir.head_norm env s, Envir.head_norm env t) of
    (Abs (ns, Ts, ts), Abs (nt, Tt, tt)) =>
      let val name = if ns = "" then nt else ns
      in unif context ((name, Ts) :: binders) (ts, tt) (unify_types context (Ts, Tt) env) end
  | (Abs (ns, Ts, ts), t) => unif context ((ns, Ts) :: binders) (ts, incr t $ Bound 0) env
  | (t, Abs (nt, Tt, tt)) => unif context ((nt, Tt) :: binders) (incr t $ Bound 0, tt) env
  | p => cases context (binders, env, p)

and cases context (binders, env, (s, t)) =
  case (strip_comb s, strip_comb t) of
    ((Var (F, Fty), ss), (Var (G, Gty), ts)) =>
      if F = G then flexflex1 (env, binders, F, Fty, ints_of' env ss, ints_of' env ts)
      else flexflex2 (env, binders, F, Fty, ints_of' env ss, G, Gty, ints_of' env ts)
  | ((Var (F, Fty), ss), _) => flexrigid context (env, binders, F, Fty, ints_of' env ss, t)
  | (_, (Var (F, Fty), ts)) => flexrigid context (env, binders, F, Fty, ints_of' env ts, s)
  | ((Const c, ss), (Const d, ts)) => rigidrigid context (env, binders, c, d, ss, ts)
  | ((Free f, ss), (Free g, ts))   => rigidrigid context (env, binders, f, g, ss, ts)
  | ((Bound i, ss), (Bound j, ts)) => rigidrigidB context (env, binders, i, j, ss, ts)
  | ((Abs _, _), _) => raise Pattern.Pattern
  | (_, (Abs _, _)) => raise Pattern.Pattern
  | ((Const (c, _), _), (Free (f, _), _)) => clash context c f
  | ((Const (c, _), _), (Bound i, _))     => clashB context binders i c
  | ((Free (f, _), _), (Const (c, _), _)) => clash context f c
  | ((Free (f, _), _), (Bound i, _))      => clashB context binders i f
  | ((Bound i, _), (Const (c, _), _))     => clashB context binders i c
  | ((Bound i, _), (Free (f, _), _))      => clashB context binders i f

and rigidrigid context (env, binders, (a, Ta), (b, Tb), ss, ts) =
  if a <> b then clash context a b
  else env |> unify_types context (Ta, Tb) |> fold (unif context binders) (ss ~~ ts)

and rigidrigidB context (env, binders, i, j, ss, ts) =
  if i <> j then clashBB context binders i j
  else fold (unif context binders) (ss ~~ ts) env

and flexrigid context (params as (env, binders, F, Fty, is, t)) =
  if occurs (F, t, env) then ocheck_fail context (F, t, binders, env)
  else
    (let val (u, env') = proj (t, env, binders, is)
     in Envir.update ((F, Fty), mkabs (binders, is, u)) env' end
     handle Unif_Diagnostic _ => proj_fail context params)

fun diagnostic_unify context = unif context []


(* ---- Formatting diagnostics ---- *)

fun format_diag_body ctxt diag =
  case diag of
    Type_Clash (T, U) =>
      let val ctxt_sorts = ctxt |> Config.put show_sorts true
          val sT = Syntax.string_of_typ ctxt_sorts T
          val sU = Syntax.string_of_typ ctxt_sorts U
      in "because type " ^ sT ^ " does not unify with " ^ sU end
  | Clash (a, b) =>
      (* If a clashing head symbol is an out-of-scope fixed variable — a skolem
         name the current context can no longer revert — explain that instead of
         dumping the raw internal name (confusing to an LLM unfamiliar with
         Isabelle internals).  The Python layer (`_postprocess_outbound_text`)
         rewrites `the out-of-scope variable <internal_name>` to the variable's
         original name plus the step that removed it. *)
      let fun outdated s = Name.is_skolem s andalso Variable.revert_fixed ctxt s = s
       in if outdated a then "because of the out-of-scope variable " ^ a
          else if outdated b then "because of the out-of-scope variable " ^ b
          else "because head symbol " ^ a ^ " clashes with " ^ b
      end
  | BoundVar_Clash (i, j) =>
      "because bound variable at depth " ^
      string_of_int i ^ " clashes with depth " ^ string_of_int j
  | Projection_Fail (F, _, _) =>
      "because variable " ^ Term.string_of_vname F ^
      " cannot be projected to match the term"
  | Occurs_Check (F, _) =>
      "because variable " ^ Term.string_of_vname F ^
      " occurs in its own unifier (occurs check)"

fun format_diagnostic ctxt fact_thm prem diag =
  let
    val fact_desc =
      if Thm.has_name_hint fact_thm
      then Minilang_Aux.simp_fact_name' (Thm_Name.print (Thm.get_name_hint fact_thm))
      else "\<open>" ^ Thm.string_of_thm ctxt fact_thm ^ "\<close>"
    val prem_str = Syntax.string_of_term ctxt prem
    val header = "the given fact " ^ fact_desc ^
                 " mismatches the target premise \<open>" ^ prem_str ^ "\<close>"
  in header ^ "\n" ^ format_diag_body ctxt diag end


(* ---- Top-level entry points ---- *)

(* Why does [lhs] (e.g. a fact's prop) not unify with [rhs] (e.g. a rule's
   premise)?  NONE = the pair is unifiable in isolation (or beyond the
   pattern fragment), so the failure must be a global/uniqueness issue. *)
fun diagnose_pair ctxt lhs rhs =
  let
    val context = Context.Proof ctxt
    val maxidx = Int.max (Term.maxidx_of_term lhs, Term.maxidx_of_term rhs)
    val env0 = Envir.empty maxidx
  in
    (diagnostic_unify context (lhs, rhs) env0; NONE)
    handle Unif_Diagnostic diag => SOME diag
         | Pattern.Pattern => NONE
  end

fun diagnose_of_failure ctxt rule facts =
  let
    val context = Context.Proof ctxt
    val prems = Thm.prems_of rule
    val nprems = length prems
    val nfacts = length facts
    val maxidx = fold (fn th => fn m => Int.max (Thm.maxidx_of th, m))
                      (rule :: facts) ~1
    val env0 = Envir.empty maxidx

    fun try_pairs _ [] _ = NONE
      | try_pairs _ _ [] = NONE
      | try_pairs env (fact :: rest_facts) (prem :: rest_prems) =
          (let val env' = diagnostic_unify context (Thm.prop_of fact, prem) env
           in try_pairs env' rest_facts rest_prems end)
          handle Unif_Diagnostic diag =>
                   SOME (format_diagnostic ctxt fact prem diag)
               | Pattern.Pattern => NONE
  in
    if nfacts > nprems then
      SOME ("more discharge facts (" ^ string_of_int nfacts ^
            ") than premises (" ^ string_of_int nprems ^ ")")
    else try_pairs env0 facts prems
  end

fun diagnose_rule_vs_goal ctxt rules goal =
  let
    val context = Context.Proof ctxt
    val goal_concl = Logic.strip_assums_concl goal

    fun try_one (eres, rule) =
      let
        val target =
          if eres then case Thm.prems_of rule of (p :: _) => SOME (Logic.strip_assums_concl p)
                                                | _ => NONE
          else SOME (Logic.strip_assums_concl (Thm.prop_of rule))
      in
        case target of NONE => NONE | SOME rule_concl =>
        let val maxidx = Int.max (Thm.maxidx_of rule, Term.maxidx_of_term goal)
            val env0 = Envir.empty maxidx
        in (diagnostic_unify context (rule_concl, goal_concl) env0; NONE)
           handle Unif_Diagnostic diag => SOME (rule, diag)
                | Pattern.Pattern => NONE
        end
      end
      handle General.Subscript => NONE

    fun first [] = NONE
      | first (r :: rs) = case try_one r of SOME x => SOME x | NONE => first rs
  in
    case first rules of
      SOME (rule, diag) =>
        let val rule_desc =
              if Thm.has_name_hint rule
              then Minilang_Aux.simp_fact_name' (Thm_Name.print (Thm.get_name_hint rule))
              else "\<open>" ^ Thm.string_of_thm ctxt rule ^ "\<close>"
        in SOME ("the conclusion of rule " ^ rule_desc ^
                 " does not match the current proof goal\n" ^
                 format_diag_body ctxt diag)
        end
    | NONE => NONE
  end

end
