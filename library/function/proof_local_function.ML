(*  Title:      Isa-Mini/library/function/proof_local_function.ML
    Author:     Qiyuan Xu (with AI assistance)
    Adapted from function_core.ML, mutual.ML, function.ML, fun.ML
    by Alexander Krauss (TU Muenchen)

Proof-local function package. Copies the standard function package
internals but replaces all theory-modifying operations with proof-local
versions that only modify the proof context, never the background theory.

===============================================================================
IMPORTANT: result-discharge timing requirement
===============================================================================

Every theorem produced by this package — simp rules, induction rules, the
function constant itself — carries local-definition hypotheses of the form
    Free (fname) \<equiv> rhs
in its Thm.hyps, one per internal constant introduced by the function
package (typically 4: fname, fname_sumC, fname_rel, fname_graph). These
hypotheses come from Local_Defs.define and are discharged only by
Proof_Context.export at a scope boundary.

It is the CALLER's responsibility to ensure that add_fun_cmd is invoked
inside a context that will eventually run Proof_Context.export from the
post-definition context back to the pre-definition context. The export
uses `def_export` to contract the definitions and remove the hyps.

Concretely, a FUN-defined function is safe to use inside any of the
following boundaries:

  * Inside an Isar `proof ... qed` block — qed runs Proof_Context.export.
  * Inside an Isar `{ ... }` block or `show ?thesis` proof — same mechanism.
  * Inside a minilang `min_script` invocation — minilang's `conclude` runs
    Proof_Context.export at the end of the script.
  * Inside a minilang `HAVE`, `INTRO`, or other scope-opening command — each
    runs its own export at END.

It is NOT safe to call add_fun_cmd in a raw Method.CONTEXT_METHOD that
returns the augmented context directly to the outer proof state without
any enclosing export point. In that case the hyps leak into the final
theorem and, in batch mode with parallel_proofs > 0, cause
`Thm.future_result: bad hyps` when the lemma's proof future is resolved.

Rule of thumb: if you can picture a `qed` or the minilang `END END`
running between `add_fun_cmd` and the final lemma theorem, you are fine.
If nothing between the call and the outer lemma closes a scope, you need
to add one yourself (a nested `proof - show ?thesis ... qed .` is enough).
*)

signature PROOF_LOCAL_FUNCTION =
sig
  val add_fun_cmd: (binding * string option * mixfix) list ->
    Specification.multi_specs_cmd -> Function_Common.function_config ->
    bool -> Proof.context -> Proof.context

  (* Phase 1 setup: prepare the pattern-completeness goal state and
     continuation, without running any tactic yet. The caller drives
     the tactic and then invokes [pat_afterqed [[proved]] ctxt] to
     proceed to the partial function context. *)
  val prepare_pat_goal:
    (binding * string option * mixfix) list ->
    Specification.multi_specs_cmd -> Function_Common.function_config ->
    bool -> Proof.context ->
    {pat_goal_state: thm,
     pat_afterqed: thm list list -> Proof.context -> Proof.context,
     lthy_after_prepare: Proof.context}

  (* Phase 2 setup: given the context after the partial function has
     been defined (i.e. after pat_afterqed has run), return the
     termination goal (as a bare Prop) and a continuation. The caller
     proves the goal and then invokes [term_afterqed [[totality]] ctxt]
     to finalize the function. *)
  val prepare_term_goal: Proof.context ->
    {term_goal: term,
     term_afterqed: thm list list -> Proof.context -> Proof.context}
end

structure Proof_Local_Function : PROOF_LOCAL_FUNCTION =
struct

open Function_Lib
open Function_Common

val trace = Unsynchronized.ref false
fun trace_msg msg = if ! trace then tracing (msg ()) else ()

val boolT = HOLogic.boolT
val mk_eq = HOLogic.mk_eq


(* ===== Adapted from function_core.ML ===== *)

datatype globals = Globals of
 {fvar: term,
  domT: typ,
  ranT: typ,
  h: term,
  y: term,
  x: term,
  z: term,
  a: term,
  P: term,
  D: term,
  Pbool:term}

datatype rec_call_info = RCInfo of
 {RIvs: (string * typ) list,
  CCas: thm list,
  rcarg: term,
  llRI: thm,
  h_assum: term}


datatype clause_context = ClauseContext of
 {ctxt : Proof.context,
  qs : term list,
  gs : term list,
  lhs: term,
  rhs: term,
  cqs: cterm list,
  ags: thm list,
  case_hyp : thm}


(* Proof-local: no transfer needed, we stay in the same context *)
fun transfer_clause_ctx _ clause = clause


datatype clause_info = ClauseInfo of
 {no: int,
  qglr : ((string * typ) list * term list * term * term),
  cdata : clause_context,
  tree: Function_Context_Tree.ctx_tree,
  lGI: thm,
  RCs: rec_call_info list}


(* Theory dependencies. *)
val acc_induct_rule = @{thm accp_induct_rule}

val ex1_implies_ex = @{thm Fun_Def.fundef_ex1_existence}
val ex1_implies_un = @{thm Fun_Def.fundef_ex1_uniqueness}
val ex1_implies_iff = @{thm Fun_Def.fundef_ex1_iff}

val acc_downward = @{thm accp_downward}
val accI = @{thm accp.accI}


fun find_calls tree =
  let
    fun add_Ri (fixes,assumes) (_ $ arg) _ (_, xs) =
      ([], (fixes, assumes, arg) :: xs)
      | add_Ri _ _ _ _ = raise Match
  in
    rev (Function_Context_Tree.traverse_tree add_Ri tree [])
  end


(** building proof obligations *)

fun mk_compat_proof_obligations domT ranT fvar f glrs =
  let
    fun mk_impl ((qs, gs, lhs, rhs),(qs', gs', lhs', rhs')) =
      let
        val shift = incr_boundvars (length qs')
      in
        Logic.mk_implies
          (HOLogic.mk_Trueprop (HOLogic.eq_const domT $ shift lhs $ lhs'),
            HOLogic.mk_Trueprop (HOLogic.eq_const ranT $ shift rhs $ rhs'))
        |> fold_rev (curry Logic.mk_implies) (map shift gs @ gs')
        |> fold_rev (fn (n,T) => fn b => Logic.all_const T $ Abs(n,T,b)) (qs @ qs')
        |> curry abstract_over fvar
        |> curry subst_bound f
      end
  in
    map mk_impl (unordered_pairs glrs)
  end


fun mk_completeness (Globals {x, Pbool, ...}) clauses qglrs =
  let
    fun mk_case (ClauseContext {qs, gs, lhs, ...}, (oqs, _, _, _)) =
      HOLogic.mk_Trueprop Pbool
      |> curry Logic.mk_implies (HOLogic.mk_Trueprop (mk_eq (x, lhs)))
      |> fold_rev (curry Logic.mk_implies) gs
      |> fold_rev mk_forall_rename (map fst oqs ~~ qs)
  in
    HOLogic.mk_Trueprop Pbool
    |> fold_rev (curry Logic.mk_implies o mk_case) (clauses ~~ qglrs)
    |> mk_forall_rename ("x", x)
    |> mk_forall_rename ("P", Pbool)
  end

(** making a context with it's own local bindings **)

fun mk_clause_context x ctxt (pre_qs,pre_gs,pre_lhs,pre_rhs) =
  let
    val (qs, ctxt') = Variable.variant_fixes (map fst pre_qs) ctxt
      |>> map2 (fn (_, T) => fn n => Free (n, T)) pre_qs

    fun inst t = subst_bounds (rev qs, t)
    val gs = map inst pre_gs
    val lhs = inst pre_lhs
    val rhs = inst pre_rhs

    val cqs = map (Thm.cterm_of ctxt') qs
    val ags = map (Thm.assume o Thm.cterm_of ctxt') gs

    val case_hyp =
      Thm.assume (Thm.cterm_of ctxt' (HOLogic.mk_Trueprop (mk_eq (x, lhs))))
  in
    ClauseContext { ctxt = ctxt', qs = qs, gs = gs, lhs = lhs, rhs = rhs,
      cqs = cqs, ags = ags, case_hyp = case_hyp }
  end


(* lowlevel term function. FIXME: remove *)
fun abstract_over_list vs body =
  let
    fun abs lev v tm =
      if v aconv tm then Bound lev
      else
        (case tm of
          Abs (a, T, t) => Abs (a, T, abs (lev + 1) v t)
        | t $ u => abs lev v t $ abs lev v u
        | t => t)
  in
    fold_index (fn (i, v) => fn t => abs i v t) vs body
  end



fun mk_clause_info globals G f no cdata qglr tree RCs GIntro_thm RIntro_thms =
  let
    val Globals {h, ...} = globals

    val ClauseContext { ctxt, qs, cqs, ags, ... } = cdata

    (* Instantiate the GIntro thm with "f" and import into the clause context. *)
    val lGI = GIntro_thm
      |> Thm.forall_elim (Thm.cterm_of ctxt f)
      |> fold Thm.forall_elim cqs
      |> fold Thm.elim_implies ags

    fun mk_call_info (rcfix, rcassm, rcarg) RI =
      let
        val llRI = RI
          |> fold Thm.forall_elim cqs
          |> fold (Thm.forall_elim o Thm.cterm_of ctxt o Free) rcfix
          |> fold Thm.elim_implies ags
          |> fold Thm.elim_implies rcassm

        val h_assum =
          HOLogic.mk_Trueprop (G $ rcarg $ (h $ rcarg))
          |> fold_rev (curry Logic.mk_implies o Thm.prop_of) rcassm
          |> fold_rev (Logic.all o Free) rcfix
          |> Pattern.rewrite_term (Proof_Context.theory_of ctxt) [(f, h)] []
          |> abstract_over_list (rev qs)
      in
        RCInfo {RIvs=rcfix, rcarg=rcarg, CCas=rcassm, llRI=llRI, h_assum=h_assum}
      end

    val RC_infos = map2 mk_call_info RCs RIntro_thms
  in
    ClauseInfo {no=no, cdata=cdata, qglr=qglr, lGI=lGI, RCs=RC_infos,
      tree=tree}
  end


fun store_compat_thms 0 thms = []
  | store_compat_thms n thms =
  let
    val (thms1, thms2) = chop n thms
  in
    (thms1 :: store_compat_thms (n - 1) thms2)
  end

(* expects i <= j *)
fun lookup_compat_thm i j cts =
  nth (nth cts (i - 1)) (j - i)

(* Returns "Gsi, Gsj, lhs_i = lhs_j |-- rhs_j_f = rhs_i_f" *)
(* if j < i, then turn around *)
fun get_compat_thm ctxt cts i j ctxi ctxj =
  let
    val ClauseContext {cqs=cqsi,ags=agsi,lhs=lhsi,...} = ctxi
    val ClauseContext {cqs=cqsj,ags=agsj,lhs=lhsj,...} = ctxj

    val lhsi_eq_lhsj = Thm.cterm_of ctxt (HOLogic.mk_Trueprop (mk_eq (lhsi, lhsj)))
  in if j < i then
    let
      val compat = lookup_compat_thm j i cts
    in
      compat         (* "!!qj qi. Gsj => Gsi => lhsj = lhsi ==> rhsj = rhsi" *)
      |> fold Thm.forall_elim (cqsj @ cqsi) (* "Gsj => Gsi => lhsj = lhsi ==> rhsj = rhsi" *)
      |> fold Thm.elim_implies agsj
      |> fold Thm.elim_implies agsi
      |> Thm.elim_implies ((Thm.assume lhsi_eq_lhsj) RS sym) (* "Gsj, Gsi, lhsi = lhsj |-- rhsj = rhsi" *)
    end
    else
    let
      val compat = lookup_compat_thm i j cts
    in
      compat        (* "!!qi qj. Gsi => Gsj => lhsi = lhsj ==> rhsi = rhsj" *)
      |> fold Thm.forall_elim (cqsi @ cqsj) (* "Gsi => Gsj => lhsi = lhsj ==> rhsi = rhsj" *)
      |> fold Thm.elim_implies agsi
      |> fold Thm.elim_implies agsj
      |> Thm.elim_implies (Thm.assume lhsi_eq_lhsj)
      |> (fn thm => thm RS sym) (* "Gsi, Gsj, lhsi = lhsj |-- rhsj = rhsi" *)
    end
  end

(* Generates the replacement lemma in fully quantified form. *)
fun mk_replacement_lemma ctxt h ih_elim clause =
  let
    val ClauseInfo {cdata=ClauseContext {qs, cqs, ags, case_hyp, ...}, RCs, tree, ...} = clause
    local open Conv in
      val ih_conv = arg1_conv o arg_conv o arg_conv
    end

    val ih_elim_case =
      Conv.fconv_rule (ih_conv (K (case_hyp RS eq_reflection))) ih_elim

    val Ris = map (fn RCInfo {llRI, ...} => llRI) RCs
    val h_assums = map (fn RCInfo {h_assum, ...} =>
      Thm.assume (Thm.cterm_of ctxt (subst_bounds (rev qs, h_assum)))) RCs

    val (eql, _) =
      Function_Context_Tree.rewrite_by_tree ctxt h ih_elim_case (Ris ~~ h_assums) tree

    val replace_lemma = HOLogic.mk_obj_eq eql
      |> Thm.implies_intr (Thm.cprop_of case_hyp)
      |> fold_rev (Thm.implies_intr o Thm.cprop_of) h_assums
      |> fold_rev (Thm.implies_intr o Thm.cprop_of) ags
      |> fold_rev Thm.forall_intr cqs
      |> Thm.close_derivation \<^here>
  in
    replace_lemma
  end


fun mk_uniqueness_clause ctxt globals compat_store clausei clausej RLj =
  let
    val thy = Proof_Context.theory_of ctxt

    val Globals {h, y, x, fvar, ...} = globals
    val ClauseInfo {no=i, cdata=cctxi as ClauseContext {ctxt=ctxti, lhs=lhsi, case_hyp, ...}, ...} =
      clausei
    val ClauseInfo {no=j, qglr=cdescj, RCs=RCsj, ...} = clausej

    val cctxj as ClauseContext {ags = agsj', lhs = lhsj', rhs = rhsj', qs = qsj', cqs = cqsj', ...} =
      mk_clause_context x ctxti cdescj

    val rhsj'h = Pattern.rewrite_term thy [(fvar,h)] [] rhsj'
    val compat = get_compat_thm ctxt compat_store i j cctxi cctxj
    val Ghsj' =
      map (fn RCInfo {h_assum, ...} =>
        Thm.assume (Thm.cterm_of ctxt (subst_bounds (rev qsj', h_assum)))) RCsj

    val RLj_import = RLj
      |> fold Thm.forall_elim cqsj'
      |> fold Thm.elim_implies agsj'
      |> fold Thm.elim_implies Ghsj'

    val y_eq_rhsj'h = Thm.assume (Thm.cterm_of ctxt (HOLogic.mk_Trueprop (mk_eq (y, rhsj'h))))
    val lhsi_eq_lhsj' = Thm.assume (Thm.cterm_of ctxt (HOLogic.mk_Trueprop (mk_eq (lhsi, lhsj'))))
       (* lhs_i = lhs_j' |-- lhs_i = lhs_j' *)
  in
    (trans OF [case_hyp, lhsi_eq_lhsj']) (* lhs_i = lhs_j' |-- x = lhs_j' *)
    |> Thm.implies_elim RLj_import
      (* Rj1' ... Rjk', lhs_i = lhs_j' |-- rhs_j'_h = rhs_j'_f *)
    |> (fn it => trans OF [it, compat])
      (* lhs_i = lhs_j', Gj', Rj1' ... Rjk' |-- rhs_j'_h = rhs_i_f *)
    |> (fn it => trans OF [y_eq_rhsj'h, it])
      (* lhs_i = lhs_j', Gj', Rj1' ... Rjk', y = rhs_j_h' |-- y = rhs_i_f *)
    |> fold_rev (Thm.implies_intr o Thm.cprop_of) Ghsj'
    |> fold_rev (Thm.implies_intr o Thm.cprop_of) agsj'
      (* lhs_i = lhs_j' , y = rhs_j_h' |-- Gj', Rj1'...Rjk' ==> y = rhs_i_f *)
    |> Thm.implies_intr (Thm.cprop_of y_eq_rhsj'h)
    |> Thm.implies_intr (Thm.cprop_of lhsi_eq_lhsj')
    |> fold_rev Thm.forall_intr (Thm.cterm_of ctxt h :: cqsj')
  end



fun mk_uniqueness_case ctxt
    globals G f ihyp ih_intro G_cases compat_store clauses rep_lemmas clausei =
  let
    val thy = Proof_Context.theory_of ctxt
    val Globals {x, y, ranT, fvar, ...} = globals
    val ClauseInfo {cdata = ClauseContext {lhs, rhs, cqs, ags, case_hyp, ...}, lGI, RCs, ...} = clausei
    val rhsC = Pattern.rewrite_term thy [(fvar, f)] [] rhs

    val ih_intro_case = full_simplify (put_simpset HOL_basic_ss ctxt addsimps [case_hyp]) ih_intro

    fun prep_RC (RCInfo {llRI, RIvs, CCas, ...}) = (llRI RS ih_intro_case)
      |> fold_rev (Thm.implies_intr o Thm.cprop_of) CCas
      |> fold_rev (Thm.forall_intr o Thm.cterm_of ctxt o Free) RIvs

    val existence = fold (curry op COMP o prep_RC) RCs lGI

    val P = Thm.cterm_of ctxt (mk_eq (y, rhsC))
    val G_lhs_y = Thm.assume (Thm.cterm_of ctxt (HOLogic.mk_Trueprop (G $ lhs $ y)))

    val unique_clauses =
      map2 (mk_uniqueness_clause ctxt globals compat_store clausei) clauses rep_lemmas

    fun elim_implies_eta A AB =
      Thm.bicompose (SOME ctxt) {flatten = false, match = true, incremented = false}
        (false, A, 0) 1 AB
      |> Seq.list_of |> the_single

    val uniqueness = G_cases
      |> Thm.forall_elim (Thm.cterm_of ctxt lhs)
      |> Thm.forall_elim (Thm.cterm_of ctxt y)
      |> Thm.forall_elim P
      |> Thm.elim_implies G_lhs_y
      |> fold elim_implies_eta unique_clauses
      |> Thm.implies_intr (Thm.cprop_of G_lhs_y)
      |> Thm.forall_intr (Thm.cterm_of ctxt y)

    val P2 = Thm.cterm_of ctxt (lambda y (G $ lhs $ y)) (* P2 y := (lhs, y): G *)

    val exactly_one =
      @{thm ex1I}
      |> Thm.instantiate'
          [SOME (Thm.ctyp_of ctxt ranT)]
          [SOME P2, SOME (Thm.cterm_of ctxt rhsC)]
      |> curry (op COMP) existence
      |> curry (op COMP) uniqueness
      |> simplify (put_simpset HOL_basic_ss ctxt addsimps [case_hyp RS sym])
      |> Thm.implies_intr (Thm.cprop_of case_hyp)
      |> fold_rev (Thm.implies_intr o Thm.cprop_of) ags
      |> fold_rev Thm.forall_intr cqs

    val function_value =
      existence
      |> Thm.implies_intr ihyp
      |> Thm.implies_intr (Thm.cprop_of case_hyp)
      |> Thm.forall_intr (Thm.cterm_of ctxt x)
      |> Thm.forall_elim (Thm.cterm_of ctxt lhs)
      |> curry (op RS) refl
  in
    (exactly_one, function_value)
  end


fun prove_stuff ctxt globals G f R clauses complete compat compat_store G_elim f_def =
  let
    val Globals {h, domT, ranT, x, ...} = globals

    (* Inductive Hypothesis: !!z. (z,x):R ==> EX!y. (z,y):G *)
    val ihyp = Logic.all_const domT $ Abs ("z", domT,
      Logic.mk_implies (HOLogic.mk_Trueprop (R $ Bound 0 $ x),
        HOLogic.mk_Trueprop (Const (\<^const_name>\<open>Ex1\<close>, (ranT --> boolT) --> boolT) $
          Abs ("y", ranT, G $ Bound 1 $ Bound 0))))
      |> Thm.cterm_of ctxt

    val ihyp_thm = Thm.assume ihyp |> Thm.forall_elim_vars 0
    val ih_intro = ihyp_thm RS (f_def RS ex1_implies_ex)
    val ih_elim = ihyp_thm RS (f_def RS ex1_implies_un)
      |> Thm.instantiate' [] [NONE, SOME (Thm.cterm_of ctxt h)]

    val _ = trace_msg (K "Proving Replacement lemmas...")
    val repLemmas = map (mk_replacement_lemma ctxt h ih_elim) clauses

    val _ = trace_msg (K "Proving cases for unique existence...")
    val (ex1s, values) =
      split_list
        (map
          (mk_uniqueness_case ctxt globals G f ihyp ih_intro G_elim compat_store clauses repLemmas)
          clauses)

    val _ = trace_msg (K "Proving: Graph is a function")
    val graph_is_function = complete
      |> Thm.forall_elim_vars 0
      |> fold (curry op COMP) ex1s
      |> Thm.implies_intr (ihyp)
      |> Thm.implies_intr (Thm.cterm_of ctxt (HOLogic.mk_Trueprop (mk_acc domT R $ x)))
      |> Thm.forall_intr (Thm.cterm_of ctxt x)
      |> (fn it => Drule.compose (it, 2, acc_induct_rule)) (* "EX! y. (?x,y):G" *)
      |> (fn it =>
          fold (Thm.forall_intr o Thm.cterm_of ctxt o Var)
            (Term.add_vars (Thm.prop_of it) []) it)

    val goalstate =  Conjunction.intr graph_is_function complete
      |> Thm.close_derivation \<^here>
      |> Goal.protect 0
      |> fold_rev (Thm.implies_intr o Thm.cprop_of) compat
      |> Thm.implies_intr (Thm.cprop_of complete)
  in
    (goalstate, values)
  end

(* wrapper -- restores quantifiers in rule specifications *)
(* Proof-local: use Inductive.gen_add_inductive with Proof_Local_Inductive.add_ind_def *)
fun inductive_def (binding as ((R, T), _)) intrs lthy =
  let
    val ({intrs = intrs_gen, elims = [elim_gen], preds = [ Rdef ], induct, ...}, lthy) =
      lthy
      |> Proof_Context.concealed
      |> Inductive.gen_add_inductive Proof_Local_Inductive.add_ind_def
          {quiet_mode = true,
            verbose = ! trace,
            alt_name = Binding.empty,
            coind = false,
            no_elim = false,
            no_ind = false,
            skip_mono = true}
          [binding] (* relation *)
          [] (* no parameters *)
          (map (fn t => (Binding.empty_atts, t)) intrs) (* intro rules *)
          [] (* no special monos *)
      ||> Proof_Context.restore_naming lthy

    fun requantify orig_intro thm =
      let
        val (qs, t) = dest_all_all orig_intro
        val frees = Variable.add_frees lthy t [] |> remove (op =) (Binding.name_of R, T)
        val vars = Term.add_vars (Thm.prop_of thm) []
        val varmap = AList.lookup (op =) (frees ~~ map fst vars)
          #> the_default ("", 0)
      in
        fold_rev (fn Free (n, T) =>
          forall_intr_rename (n, Thm.cterm_of lthy (Var (varmap (n, T), T)))) qs thm
      end
  in
    ((Rdef, map2 requantify intrs intrs_gen, Thm.forall_intr_vars elim_gen, induct), lthy)
  end

fun define_graph (G_binding, G_type) fvar clauses RCss lthy =
  let
    val G = Free (Binding.name_of G_binding, G_type)
    fun mk_GIntro (ClauseContext {qs, gs, lhs, rhs, ...}) RCs =
      let
        fun mk_h_assm (rcfix, rcassm, rcarg) =
          HOLogic.mk_Trueprop (G $ rcarg $ (fvar $ rcarg))
          |> fold_rev (curry Logic.mk_implies o Thm.prop_of) rcassm
          |> fold_rev (Logic.all o Free) rcfix
      in
        HOLogic.mk_Trueprop (G $ lhs $ rhs)
        |> fold_rev (curry Logic.mk_implies o mk_h_assm) RCs
        |> fold_rev (curry Logic.mk_implies) gs
        |> fold_rev Logic.all (fvar :: qs)
      end

    val G_intros = map2 mk_GIntro clauses RCss
  in inductive_def ((G_binding, G_type), NoSyn) G_intros lthy end

(* Proof-local: use Proof_Local_Lthy.define instead of Local_Theory.define *)
fun define_function defname (fname, mixfix) domT ranT G default lthy =
  let
    val f_def_binding =
      Thm.make_def_binding (Config.get lthy function_internals)
        (derived_name_suffix defname "_sumC")
    val f_def =
      Abs ("x", domT, Const (\<^const_name>\<open>Fun_Def.THE_default\<close>, ranT --> (ranT --> boolT) --> ranT)
        $ (default $ Bound 0) $ Abs ("y", ranT, G $ Bound 1 $ Bound 0))
      |> Syntax.check_term lthy
  in
    lthy |> Proof_Local_Lthy.define
      ((Binding.map_name (suffix "C") fname, mixfix), ((f_def_binding, []), f_def))
  end

fun define_recursion_relation (R_binding, R_type) qglrs clauses RCss lthy =
  let
    val R = Free (Binding.name_of R_binding, R_type)
    fun mk_RIntro (ClauseContext {qs, gs, lhs, ...}, (oqs, _, _, _)) (rcfix, rcassm, rcarg) =
      HOLogic.mk_Trueprop (R $ rcarg $ lhs)
      |> fold_rev (curry Logic.mk_implies o Thm.prop_of) rcassm
      |> fold_rev (curry Logic.mk_implies) gs
      |> fold_rev (Logic.all o Free) rcfix
      |> fold_rev mk_forall_rename (map fst oqs ~~ qs)
      (* "!!qs xs. CS ==> G => (r, lhs) : R" *)

    val R_intross = map2 (map o mk_RIntro) (clauses ~~ qglrs) RCss

    val ((R, RIntro_thms, R_elim, _), lthy) =
      inductive_def ((R_binding, R_type), NoSyn) (flat R_intross) lthy
  in
    ((R, Library.unflat R_intross RIntro_thms, R_elim), lthy)
  end


fun fix_globals domT ranT fvar ctxt =
  let
    val ([h, y, x, z, a, D, P, Pbool], ctxt') = Variable.variant_fixes
      ["h_fd", "y_fd", "x_fd", "z_fd", "a_fd", "D_fd", "P_fd", "Pb_fd"] ctxt
  in
    (Globals {h = Free (h, domT --> ranT),
      y = Free (y, ranT),
      x = Free (x, domT),
      z = Free (z, domT),
      a = Free (a, domT),
      D = Free (D, domT --> boolT),
      P = Free (P, domT --> boolT),
      Pbool = Free (Pbool, boolT),
      fvar = fvar,
      domT = domT,
      ranT = ranT},
    ctxt')
  end

fun inst_RC ctxt fvar f (rcfix, rcassm, rcarg) =
  let
    fun inst_term t = subst_bound(f, abstract_over (fvar, t))
  in
    (rcfix, map (Thm.assume o Thm.cterm_of ctxt o inst_term o Thm.prop_of) rcassm, inst_term rcarg)
  end



(**********************************************************
 *                   PROVING THE RULES
 **********************************************************)

fun mk_psimps ctxt globals R clauses valthms f_iff graph_is_function =
  let
    val Globals {domT, z, ...} = globals

    fun mk_psimp
      (ClauseInfo {qglr = (oqs, _, _, _), cdata = ClauseContext {cqs, lhs, ags, ...}, ...}) valthm =
      let
        val lhs_acc =
          Thm.cterm_of ctxt (HOLogic.mk_Trueprop (mk_acc domT R $ lhs)) (* "acc R lhs" *)
        val z_smaller =
          Thm.cterm_of ctxt (HOLogic.mk_Trueprop (R $ z $ lhs)) (* "R z lhs" *)
      in
        ((Thm.assume z_smaller) RS ((Thm.assume lhs_acc) RS acc_downward))
        |> (fn it => it COMP graph_is_function)
        |> Thm.implies_intr z_smaller
        |> Thm.forall_intr (Thm.cterm_of ctxt  z)
        |> (fn it => it COMP valthm)
        |> Thm.implies_intr lhs_acc
        |> asm_simplify (put_simpset HOL_basic_ss ctxt addsimps [f_iff])
        |> fold_rev (Thm.implies_intr o Thm.cprop_of) ags
        |> fold_rev forall_intr_rename (map fst oqs ~~ cqs)
      end
  in
    map2 mk_psimp clauses valthms
  end


(** Induction rule **)


val acc_subset_induct = @{thm predicate1I} RS @{thm accp_subset_induct}


fun mk_partial_induct_rule ctxt globals R complete_thm clauses =
  let
    val Globals {domT, x, z, a, P, D, ...} = globals
    val acc_R = mk_acc domT R

    val x_D = Thm.assume (Thm.cterm_of ctxt (HOLogic.mk_Trueprop (D $ x)))
    val a_D = Thm.cterm_of ctxt (HOLogic.mk_Trueprop (D $ a))

    val D_subset =
      Thm.cterm_of ctxt (Logic.all x
        (Logic.mk_implies (HOLogic.mk_Trueprop (D $ x), HOLogic.mk_Trueprop (acc_R $ x))))

    val D_dcl = (* "!!x z. [| x: D; (z,x):R |] ==> z:D" *)
      Logic.all x (Logic.all z (Logic.mk_implies (HOLogic.mk_Trueprop (D $ x),
        Logic.mk_implies (HOLogic.mk_Trueprop (R $ z $ x),
          HOLogic.mk_Trueprop (D $ z)))))
      |> Thm.cterm_of ctxt

    (* Inductive Hypothesis: !!z. (z,x):R ==> P z *)
    val ihyp = Logic.all_const domT $ Abs ("z", domT,
      Logic.mk_implies (HOLogic.mk_Trueprop (R $ Bound 0 $ x),
        HOLogic.mk_Trueprop (P $ Bound 0)))
      |> Thm.cterm_of ctxt

    val aihyp = Thm.assume ihyp

    fun prove_case clause =
      let
        val ClauseInfo {cdata = ClauseContext {ctxt = ctxt1, qs, cqs, ags, gs, lhs, case_hyp, ...},
          RCs, qglr = (oqs, _, _, _), ...} = clause

        val case_hyp_conv = K (case_hyp RS eq_reflection)
        local open Conv in
          val lhs_D = fconv_rule (arg_conv (arg_conv (case_hyp_conv))) x_D
          val sih =
            fconv_rule
              (binder_conv (K (arg1_conv (arg_conv (arg_conv case_hyp_conv)))) ctxt1) aihyp
        end

        fun mk_Prec (RCInfo {llRI, RIvs, CCas, rcarg, ...}) = sih
          |> Thm.forall_elim (Thm.cterm_of ctxt rcarg)
          |> Thm.elim_implies llRI
          |> fold_rev (Thm.implies_intr o Thm.cprop_of) CCas
          |> fold_rev (Thm.forall_intr o Thm.cterm_of ctxt o Free) RIvs

        val P_recs = map mk_Prec RCs   (*  [P rec1, P rec2, ... ]  *)

        val step = HOLogic.mk_Trueprop (P $ lhs)
          |> fold_rev (curry Logic.mk_implies o Thm.prop_of) P_recs
          |> fold_rev (curry Logic.mk_implies) gs
          |> curry Logic.mk_implies (HOLogic.mk_Trueprop (D $ lhs))
          |> fold_rev mk_forall_rename (map fst oqs ~~ qs)
          |> Thm.cterm_of ctxt

        val P_lhs = Thm.assume step
          |> fold Thm.forall_elim cqs
          |> Thm.elim_implies lhs_D
          |> fold Thm.elim_implies ags
          |> fold Thm.elim_implies P_recs

        val res = Thm.cterm_of ctxt (HOLogic.mk_Trueprop (P $ x))
          |> Conv.arg_conv (Conv.arg_conv case_hyp_conv)
          |> Thm.symmetric (* P lhs == P x *)
          |> (fn eql => Thm.equal_elim eql P_lhs) (* "P x" *)
          |> Thm.implies_intr (Thm.cprop_of case_hyp)
          |> fold_rev (Thm.implies_intr o Thm.cprop_of) ags
          |> fold_rev Thm.forall_intr cqs
      in
        (res, step)
      end

    val (cases, steps) = split_list (map prove_case clauses)

    val istep = complete_thm
      |> Thm.forall_elim_vars 0
      |> fold (curry op COMP) cases (*  P x  *)
      |> Thm.implies_intr ihyp
      |> Thm.implies_intr (Thm.cprop_of x_D)
      |> Thm.forall_intr (Thm.cterm_of ctxt x)

    val subset_induct_rule =
      acc_subset_induct
      |> (curry op COMP) (Thm.assume D_subset)
      |> (curry op COMP) (Thm.assume D_dcl)
      |> (curry op COMP) (Thm.assume a_D)
      |> (curry op COMP) istep
      |> fold_rev Thm.implies_intr steps
      |> Thm.implies_intr a_D
      |> Thm.implies_intr D_dcl
      |> Thm.implies_intr D_subset

    val simple_induct_rule =
      subset_induct_rule
      |> Thm.forall_intr (Thm.cterm_of ctxt D)
      |> Thm.forall_elim (Thm.cterm_of ctxt acc_R)
      |> assume_tac ctxt 1 |> Seq.hd
      |> (curry op COMP) (acc_downward
        |> (Thm.instantiate' [SOME (Thm.ctyp_of ctxt domT)] (map (SOME o Thm.cterm_of ctxt) [R, x, z]))
        |> Thm.forall_intr (Thm.cterm_of ctxt z)
        |> Thm.forall_intr (Thm.cterm_of ctxt x))
      |> Thm.forall_intr (Thm.cterm_of ctxt a)
      |> Thm.forall_intr (Thm.cterm_of ctxt P)
  in
    simple_induct_rule
  end


(* FIXME: broken by design *)
fun mk_domain_intro ctxt (Globals {domT, ...}) R R_cases clause =
  let
    val ClauseInfo {cdata = ClauseContext {gs, lhs, cqs, ...},
      qglr = (oqs, _, _, _), ...} = clause
    val goal = HOLogic.mk_Trueprop (mk_acc domT R $ lhs)
      |> fold_rev (curry Logic.mk_implies) gs
      |> Thm.cterm_of ctxt
  in
    Goal.init goal
    |> (SINGLE (resolve_tac ctxt [accI] 1)) |> the
    |> (SINGLE (eresolve_tac ctxt [Thm.forall_elim_vars 0 R_cases] 1))  |> the
    |> (SINGLE (auto_tac ctxt)) |> the
    |> Goal.conclude
    |> fold_rev forall_intr_rename (map fst oqs ~~ cqs)
  end



(** Termination rule **)

val wf_induct_rule = @{thm Wellfounded.wfP_induct_rule}
val wf_in_rel = @{thm Fun_Def.wf_in_rel}
val in_rel_def = @{thm Fun_Def.in_rel_def}

fun mk_nest_term_case ctxt globals R' ihyp clause =
  let
    val Globals {z, ...} = globals
    val ClauseInfo {cdata = ClauseContext {qs, cqs, ags, lhs, case_hyp, ...}, tree,
      qglr=(oqs, _, _, _), ...} = clause

    val ih_case = full_simplify (put_simpset HOL_basic_ss ctxt addsimps [case_hyp]) ihyp

    fun step (fixes, assumes) (_ $ arg) u (sub,(hyps,thms)) =
      let
        val used = (u @ sub)
          |> map (fn (ctx, thm) => Function_Context_Tree.export_thm ctxt ctx thm)

        val hyp = HOLogic.mk_Trueprop (R' $ arg $ lhs)
          |> fold_rev (curry Logic.mk_implies o Thm.prop_of) used (* additional hyps *)
          |> Function_Context_Tree.export_term (fixes, assumes)
          |> fold_rev (curry Logic.mk_implies o Thm.prop_of) ags
          |> fold_rev mk_forall_rename (map fst oqs ~~ qs)
          |> Thm.cterm_of ctxt

        val thm = Thm.assume hyp
          |> fold Thm.forall_elim cqs
          |> fold Thm.elim_implies ags
          |> Function_Context_Tree.import_thm ctxt (fixes, assumes)
          |> fold Thm.elim_implies used (*  "(arg, lhs) : R'"  *)

        val z_eq_arg = HOLogic.mk_Trueprop (mk_eq (z, arg))
          |> Thm.cterm_of ctxt |> Thm.assume

        val acc = thm COMP ih_case
        val z_acc_local = acc
          |> Conv.fconv_rule
              (Conv.arg_conv (Conv.arg_conv (K (Thm.symmetric (z_eq_arg RS eq_reflection)))))

        val ethm = z_acc_local
          |> Function_Context_Tree.export_thm ctxt (fixes,
               z_eq_arg :: case_hyp :: ags @ assumes)
          |> fold_rev forall_intr_rename (map fst oqs ~~ cqs)

        val sub' = sub @ [(([],[]), acc)]
      in
        (sub', (hyp :: hyps, ethm :: thms))
      end
      | step _ _ _ _ = raise Match
  in
    Function_Context_Tree.traverse_tree step tree
  end


fun mk_nest_term_rule ctxt globals R R_cases clauses =
  let
    val Globals { domT, x, z, ... } = globals
    val acc_R = mk_acc domT R

    val ([Rn], ctxt') = Variable.variant_fixes ["R"] ctxt
    val R' = Free (Rn, fastype_of R)

    val Rrel = Free (Rn, HOLogic.mk_setT (HOLogic.mk_prodT (domT, domT)))
    val inrel_R = Const (\<^const_name>\<open>Fun_Def.in_rel\<close>,
      HOLogic.mk_setT (HOLogic.mk_prodT (domT, domT)) --> fastype_of R) $ Rrel

    val wfR' = HOLogic.mk_Trueprop (Const (\<^const_abbrev>\<open>Wellfounded.wfP\<close>,
      (domT --> domT --> boolT) --> boolT) $ R')
      |> Thm.cterm_of ctxt' (* "wf R'" *)

    (* Inductive Hypothesis: !!z. (z,x):R' ==> z : acc R *)
    val ihyp = Logic.all_const domT $ Abs ("z", domT,
      Logic.mk_implies (HOLogic.mk_Trueprop (R' $ Bound 0 $ x),
        HOLogic.mk_Trueprop (acc_R $ Bound 0)))
      |> Thm.cterm_of ctxt'

    val ihyp_a = Thm.assume ihyp |> Thm.forall_elim_vars 0

    val R_z_x = Thm.cterm_of ctxt' (HOLogic.mk_Trueprop (R $ z $ x))

    val (hyps, cases) = fold (mk_nest_term_case ctxt' globals R' ihyp_a) clauses ([], [])
  in
    R_cases
    |> Thm.forall_elim (Thm.cterm_of ctxt' z)
    |> Thm.forall_elim (Thm.cterm_of ctxt' x)
    |> Thm.forall_elim (Thm.cterm_of ctxt' (acc_R $ z))
    |> curry op COMP (Thm.assume R_z_x)
    |> fold_rev (curry op COMP) cases
    |> Thm.implies_intr R_z_x
    |> Thm.forall_intr (Thm.cterm_of ctxt' z)
    |> (fn it => it COMP accI)
    |> Thm.implies_intr ihyp
    |> Thm.forall_intr (Thm.cterm_of ctxt' x)
    |> (fn it => Drule.compose (it, 2, wf_induct_rule))
    |> curry op RS (Thm.assume wfR')
    |> Thm.forall_intr_vars
    |> (fn it => it COMP allI)
    |> fold Thm.implies_intr hyps
    |> Thm.implies_intr wfR'
    |> Thm.forall_intr (Thm.cterm_of ctxt' R')
    |> Thm.forall_elim (Thm.cterm_of ctxt' inrel_R)
    |> curry op RS wf_in_rel
    |> full_simplify (put_simpset HOL_basic_ss ctxt' addsimps [in_rel_def])
    |> Thm.forall_intr_name ("R", Thm.cterm_of ctxt' Rrel)
  end



fun prepare_function config defname [((fname, fT), mixfix)] abstract_qglrs lthy =
  let
    val FunctionConfig {domintros, default=default_opt, ...} = config

    val default_str = the_default "%x. HOL.undefined" (* FIXME proper term!? *) default_opt
    val fvar = (Binding.name_of fname, fT)
    val domT = domain_type fT
    val ranT = range_type fT

    val default = Syntax.parse_term lthy default_str
      |> Type.constraint fT |> Syntax.check_term lthy

    val (globals, ctxt') = fix_globals domT ranT (Free fvar) lthy

    val Globals { x, h, ... } = globals

    val clauses = map (mk_clause_context x ctxt') abstract_qglrs

    val n = length abstract_qglrs

    fun build_tree (ClauseContext { ctxt, rhs, ...}) =
       Function_Context_Tree.mk_tree (Free fvar) h ctxt rhs

    val trees = map build_tree clauses
    val RCss = map find_calls trees

    val ((G, GIntro_thms, G_elim, G_induct), lthy) =
      PROFILE "def_graph"
        (define_graph
          (derived_name_suffix defname "_graph", domT --> ranT --> boolT) (Free fvar) clauses RCss)
        lthy

    val ((f, (_, f_defthm)), lthy) =
      PROFILE "def_fun" (define_function defname (fname, mixfix) domT ranT G default) lthy

    val RCss = map (map (inst_RC lthy (Free fvar) f)) RCss
    val trees = map (Function_Context_Tree.inst_tree lthy (Free fvar) f) trees

    val ((R, RIntro_thmss, R_elim), lthy) =
      PROFILE "def_rel"
        (define_recursion_relation (derived_name_suffix defname "_rel", domT --> domT --> boolT)
          abstract_qglrs clauses RCss) lthy

    val dom = mk_acc domT R

    (* Proof-local: skip Local_Theory.abbrev for _dom — dom is already available as a term *)

    val clauses = map (transfer_clause_ctx ()) clauses

    val xclauses = PROFILE "xclauses"
      (@{map 7} (mk_clause_info globals G f) (1 upto n) clauses abstract_qglrs trees
        RCss GIntro_thms) RIntro_thmss

    val complete =
      mk_completeness globals clauses abstract_qglrs |> Thm.cterm_of lthy |> Thm.assume

    val compat =
      mk_compat_proof_obligations domT ranT (Free fvar) f abstract_qglrs
      |> map (Thm.cterm_of lthy #> Thm.assume)

    val compat_store = store_compat_thms n compat

    val (goalstate, values) = PROFILE "prove_stuff"
      (prove_stuff lthy globals G f R xclauses complete compat
         compat_store G_elim) f_defthm

    fun mk_partial_rules newctxt provedgoal =
      let
        val (graph_is_function, complete_thm) =
          provedgoal
          |> Conjunction.elim
          |> apfst (Thm.forall_elim_vars 0)

        val f_iff = graph_is_function RS (f_defthm RS ex1_implies_iff)

        val psimps = PROFILE "Proving simplification rules"
          (mk_psimps newctxt globals R xclauses values f_iff) graph_is_function

        val simple_pinduct = PROFILE "Proving partial induction rule"
          (mk_partial_induct_rule newctxt globals R complete_thm) xclauses

        val total_intro = PROFILE "Proving nested termination rule"
          (mk_nest_term_rule newctxt globals R R_elim) xclauses

        val dom_intros =
          if domintros then SOME (PROFILE "Proving domain introduction rules"
             (map (mk_domain_intro lthy globals R R_elim)) xclauses)
           else NONE
      in
        FunctionResult {fs=[f], G=G, R=R, dom=dom,
          cases=[complete_thm], psimps=psimps, pelims=[],
          simple_pinducts=[simple_pinduct],
          termination=total_intro, domintros=dom_intros}
      end
  in
    ((f, goalstate, mk_partial_rules), lthy)
  end
  | prepare_function _ _ _ _ _ = error "prepare_function: expected single function"


(* ===== Adapted from mutual.ML ===== *)

type qgar = string * (string * typ) list * term list * term list * term

datatype mutual_part = MutualPart of
 {i : int,
  i' : int,
  fname : binding,
  fT : typ,
  cargTs: typ list,
  f_def: term,

  f: term option,
  f_defthm : thm option}

datatype mutual_info = Mutual of
 {n : int,
  n' : int,
  fsum_name : binding,
  fsum_type: typ,

  ST: typ,
  RST: typ,

  parts: mutual_part list,
  fqgars: qgar list,
  qglrs: ((string * typ) list * term list * term * term) list,

  fsum : term option}

fun mutual_induct_Pnames n =
  if n < 5 then fst (chop n ["P","Q","R","S"])
  else map (fn i => "P" ^ string_of_int i) (1 upto n)

fun get_part f =
  the o find_first (fn (MutualPart {fname, ...}) => Binding.name_of fname = f)

(* FIXME *)
fun mk_prod_abs e (t1, t2) =
  let
    val bTs = rev (map snd e)
    val T1 = fastype_of1 (bTs, t1)
    val T2 = fastype_of1 (bTs, t2)
  in
    HOLogic.pair_const T1 T2 $ t1 $ t2
  end

fun analyze_eqs ctxt defname fs eqs =
  let
    val num = length fs
    val fqgars = map (split_def ctxt (K true)) eqs
    fun arity_of fname =
      the (get_first (fn (f, _, _, args, _) =>
        if f = Binding.name_of fname then SOME (length args) else NONE) fqgars)

    fun curried_types (fname, fT) =
      let val (caTs, uaTs) = chop (arity_of fname) (binder_types fT)
      in (caTs, uaTs ---> body_type fT) end

    val (caTss, resultTs) = split_list (map curried_types fs)
    val argTs = map (foldr1 HOLogic.mk_prodT) caTss

    val dresultTs = distinct (op =) resultTs
    val n' = length dresultTs

    val RST = Balanced_Tree.make (uncurry Sum_Tree.mk_sumT) dresultTs
    val ST = Balanced_Tree.make (uncurry Sum_Tree.mk_sumT) argTs

    val fsum_name = derived_name_suffix defname "_sum"
    val ([fsum_var_name], _) = Variable.add_fixes_binding [fsum_name] ctxt
    val fsum_type = ST --> RST
    val fsum_var = (fsum_var_name, fsum_type)

    fun define (fname, fT) caTs resultT i =
      let
        val vars = map_index (fn (j,T) => Free ("x" ^ string_of_int j, T)) caTs (* FIXME: Bind xs properly *)
        val i' = find_index (fn Ta => Ta = resultT) dresultTs + 1

        val f_exp = Sum_Tree.mk_proj RST n' i' (Free fsum_var $ Sum_Tree.mk_inj ST num i (foldr1 HOLogic.mk_prod vars))
        val def = Term.abstract_over (Free fsum_var, fold_rev lambda vars f_exp)

        val rew = (Binding.name_of fname, fold_rev lambda vars f_exp)
      in
        (MutualPart
          {i = i, i' = i', fname = fname, fT = fT, cargTs = caTs,
            f_def = def, f = NONE, f_defthm = NONE}, rew)
      end

    val (parts, rews) = split_list (@{map 4} define fs caTss resultTs (1 upto num))

    fun convert_eqs (f, qs, gs, args, rhs) =
      let
        val MutualPart {i, i', ...} = get_part f parts
        val rhs' = rhs
          |> map_aterms (fn t as Free (n, _) => the_default t (AList.lookup (op =) rews n) | t => t)
      in
        (qs, gs, Sum_Tree.mk_inj ST num i (foldr1 (mk_prod_abs qs) args),
         Envir.beta_norm (Sum_Tree.mk_inj RST n' i' rhs'))
      end

    val qglrs = map convert_eqs fqgars
  in
    Mutual {n = num, n' = n', fsum_name = fsum_name, fsum_type = fsum_type,
      ST = ST, RST = RST, parts = parts, fqgars = fqgars, qglrs = qglrs, fsum = NONE}
  end

(* Proof-local: use Proof_Local_Lthy.define instead of Local_Theory.define *)
fun define_projections fixes mutual fsum lthy =
  let
    fun def ((MutualPart {i=i, i'=i', fname, fT, cargTs, f_def, ...}), (_, mixfix)) lthy =
      let
        val def_binding = Thm.make_def_binding (Config.get lthy function_internals) fname
        val ((f, (_, f_defthm)), lthy') =
          Proof_Local_Lthy.define
            ((fname, mixfix), ((def_binding, []), Term.subst_bound (fsum, f_def))) lthy
      in
        (MutualPart {i = i, i' = i', fname = fname, fT = fT, cargTs = cargTs,
            f_def = f_def, f = SOME f, f_defthm = SOME f_defthm}, lthy')
      end

    val Mutual {n, n', fsum_name, fsum_type, ST, RST, parts, fqgars, qglrs, ...} = mutual
    val (parts', lthy') = fold_map def (parts ~~ fixes) lthy
  in
    (Mutual {n = n, n' = n', fsum_name = fsum_name, fsum_type = fsum_type, ST = ST,
      RST = RST, parts = parts', fqgars = fqgars, qglrs = qglrs, fsum = SOME fsum}, lthy')
  end

fun in_context ctxt (f, pre_qs, pre_gs, pre_args, pre_rhs) F =
  let
    val oqnames = map fst pre_qs
    val (qs, _) = Variable.variant_fixes oqnames ctxt
      |>> map2 (fn (_, T) => fn n => Free (n, T)) pre_qs

    fun inst t = subst_bounds (rev qs, t)
    val gs = map inst pre_gs
    val args = map inst pre_args
    val rhs = inst pre_rhs

    val cqs = map (Thm.cterm_of ctxt) qs
    val ags = map (Thm.assume o Thm.cterm_of ctxt) gs

    val import = fold Thm.forall_elim cqs
      #> fold Thm.elim_implies ags

    val export = fold_rev (Thm.implies_intr o Thm.cprop_of) ags
      #> fold_rev forall_intr_rename (oqnames ~~ cqs)
  in
    F ctxt (f, qs, gs, args, rhs) import export
  end

fun recover_mutual_psimp all_orig_fdefs parts ctxt (fname, _, _, args, rhs)
    import (export : thm -> thm) sum_psimp_eq =
  let
    val (MutualPart {f=SOME f, ...}) = get_part fname parts

    val psimp = import sum_psimp_eq
    val (simp, restore_cond) =
      case cprems_of psimp of
        [] => (psimp, I)
      | [cond] => (Thm.implies_elim psimp (Thm.assume cond), Thm.implies_intr cond)
      | _ => raise General.Fail "Too many conditions"

    val simp_ctxt = fold Thm.declare_hyps (Thm.chyps_of simp) ctxt
  in
    Goal.prove simp_ctxt [] []
      (HOLogic.Trueprop $ HOLogic.mk_eq (list_comb (f, args), rhs))
      (fn _ =>
        Local_Defs.unfold0_tac ctxt all_orig_fdefs
          THEN EqSubst.eqsubst_tac ctxt [0] [simp] 1
          THEN (simp_tac ctxt) 1)
    |> restore_cond
    |> export
  end

fun mk_applied_form ctxt caTs thm =
  let
    val xs =
      map_index (fn (i, T) =>
        Thm.cterm_of ctxt
          (Free ("x" ^ string_of_int i, T))) caTs (* FIXME: Bind xs properly *)
  in
    fold (fn x => fn thm => Thm.combination thm (Thm.reflexive x)) xs thm
    |> Conv.fconv_rule (Thm.beta_conversion true)
    |> fold_rev Thm.forall_intr xs
    |> Thm.forall_elim_vars 0
  end

fun mutual_induct_rules ctxt induct all_f_defs (Mutual {n, ST, parts, ...}) =
  let
    val newPs =
      map2 (fn Pname => fn MutualPart {cargTs, ...} =>
          Free (Pname, cargTs ---> HOLogic.boolT))
        (mutual_induct_Pnames (length parts)) parts

    fun mk_P (MutualPart {cargTs, ...}) P =
      let
        val avars = map_index (fn (i,T) => Var (("a", i), T)) cargTs
        val atup = foldr1 HOLogic.mk_prod avars
      in
        HOLogic.tupled_lambda atup (list_comb (P, avars))
      end

    val Ps = map2 mk_P parts newPs
    val case_exp = Sum_Tree.mk_sumcases HOLogic.boolT Ps

    val induct_inst =
      Thm.forall_elim (Thm.cterm_of ctxt case_exp) induct
      |> full_simplify (put_simpset Sum_Tree.sumcase_split_ss ctxt)
      |> full_simplify (put_simpset HOL_basic_ss ctxt addsimps all_f_defs)

    fun project rule (MutualPart {cargTs, i, ...}) k =
      let
        val afs = map_index (fn (j,T) => Free ("a" ^ string_of_int (j + k), T)) cargTs (* FIXME! *)
        val inj = Sum_Tree.mk_inj ST n i (foldr1 HOLogic.mk_prod afs)
      in
        (rule
         |> Thm.forall_elim (Thm.cterm_of ctxt inj)
         |> full_simplify (put_simpset Sum_Tree.sumcase_split_ss ctxt)
         |> fold_rev (Thm.forall_intr o Thm.cterm_of ctxt) (afs @ newPs),
         k + length cargTs)
      end
  in
    fst (fold_map (project induct_inst) parts 0)
  end

fun mutual_cases_rule ctxt cases_rule n ST (MutualPart {i, cargTs = Ts, ...}) =
  let
    val [P, x] =
      Variable.variant_frees ctxt [] [("P", \<^typ>\<open>bool\<close>), ("x", HOLogic.mk_tupleT Ts)]
      |> map (Thm.cterm_of ctxt o Free);
    val sumtree_inj = Thm.cterm_of ctxt (Sum_Tree.mk_inj ST n i (Thm.term_of x));

    fun prep_subgoal_tac i =
      REPEAT (eresolve_tac ctxt
        @{thms Pair_inject Inl_inject [elim_format] Inr_inject [elim_format]} i)
      THEN REPEAT (eresolve_tac ctxt
        @{thms HOL.notE [OF Sum_Type.sum.distinct(1)] HOL.notE [OF Sum_Type.sum.distinct(2)]} i);
  in
    cases_rule
    |> Thm.forall_elim P
    |> Thm.forall_elim sumtree_inj
    |> Tactic.rule_by_tactic ctxt (ALLGOALS prep_subgoal_tac)
    |> Thm.forall_intr x
    |> Thm.forall_intr P
    |> Thm.solve_constraints
  end


fun mk_partial_rules_mutual lthy inner_cont (m as Mutual {parts, fqgars, n, ST, ...}) proof =
  let
    val result = inner_cont proof
    val FunctionResult {G, R, cases=[cases_rule], psimps, simple_pinducts=[simple_pinduct],
      termination, domintros, dom, pelims, ...} = result

    val (all_f_defs, fs) =
      map (fn MutualPart {f_defthm = SOME f_def, f = SOME f, cargTs, ...} =>
        (mk_applied_form lthy cargTs (Thm.symmetric f_def), f))
      parts
      |> split_list

    val all_orig_fdefs =
      map (fn MutualPart {f_defthm = SOME f_def, ...} => f_def) parts

    fun mk_mpsimp fqgar sum_psimp =
      in_context lthy fqgar (recover_mutual_psimp all_orig_fdefs parts) sum_psimp

    val rew_simpset = put_simpset HOL_basic_ss lthy addsimps all_f_defs
    val mpsimps = map2 mk_mpsimp fqgars psimps
    val minducts = mutual_induct_rules lthy simple_pinduct all_f_defs m
    val mcases = map (mutual_cases_rule lthy cases_rule n ST) parts
    val mtermination = full_simplify rew_simpset termination
    val mdomintros = Option.map (map (full_simplify rew_simpset)) domintros

  in
    FunctionResult { fs=fs, G=G, R=R, dom=dom,
      psimps=mpsimps, simple_pinducts=minducts,
      cases=mcases, pelims=pelims, termination=mtermination,
      domintros=mdomintros}
  end


(* Proof-local: use our local prepare_function instead of Function_Core.prepare_function *)
fun prepare_function_mutual config defname fixes eqss lthy =
  let
    val mutual as Mutual {fsum_name, fsum_type, qglrs, ...} =
      analyze_eqs lthy defname (map fst fixes) (map Envir.beta_eta_contract eqss)

    val ((fsum, goalstate, cont), lthy') =
      prepare_function config defname [((fsum_name, fsum_type), NoSyn)] qglrs lthy

    val (mutual', lthy'') = define_projections fixes mutual fsum lthy'

    fun cont' ctxt = mk_partial_rules_mutual lthy'' (cont ctxt) mutual'
  in
    ((goalstate, cont'), lthy'')
  end


(* ===== Adapted from function.ML ===== *)

val simp_attribs =
  @{attributes [simp, nitpick_simp]}

val psimp_attribs =
  @{attributes [nitpick_psimp]}

(* Proof-local: use Proof_Local_Lthy.note instead of Local_Theory.note *)
fun note_derived (a, atts) (fname, thms) =
  Proof_Local_Lthy.note ((derived_name fname a, atts), thms) #> apfst snd

(* Proof-local: use Proof_Local_Lthy.note instead of Local_Theory.note *)
fun add_simps fnames post sort extra_qualify label mod_binding moreatts simps lthy =
  let
    val spec = post simps
      |> map (apfst (apsnd (fn ats => moreatts @ ats)))
      |> map (apfst (apfst extra_qualify))

    val (saved_spec_simps, lthy') =
      fold_map Proof_Local_Lthy.note spec lthy

    val saved_simps = maps snd saved_spec_simps
    val simps_by_f = sort saved_simps

    fun note fname simps =
      Proof_Local_Lthy.note ((mod_binding (derived_name fname label), []), simps) #> snd
  in (saved_simps, fold2 note fnames simps_by_f lthy') end

fun prepare_function_top do_print prep fixspec eqns config lthy =
  let
    val ((fixes0, spec0), ctxt') = prep fixspec eqns lthy
    val fixes = map (apfst (apfst Binding.name_of)) fixes0
    val spec = map (fn (bnd, prop) => (bnd, [prop])) spec0
    val (eqs, post, sort_cont, cnames) = get_preproc lthy config ctxt' fixes spec

    val fnames = map (fst o fst) fixes0
    val defname = Binding.conglomerate fnames;

    val FunctionConfig {partials, default, ...} = config
    val _ =
      if is_some default
      then legacy_feature "\"function (default)\" -- use 'partial_function' instead"
      else ()

    val ((goal_state, cont), lthy') =
      prepare_function_mutual config defname fixes0 eqs lthy

    fun afterqed [[proof]] lthy1 =
      let
        val result = cont lthy1 (Thm.close_derivation \<^here> proof)
        val FunctionResult {fs, R, dom, psimps, simple_pinducts,
                termination, domintros, cases, ...} = result

        val pelims = Function_Elims.mk_partial_elim_rules lthy1 result

        val concealed_partial = if partials then I else Binding.concealed

        val addsmps = add_simps fnames post sort_cont

        (* Proof-local: use Proof_Local_Lthy.notes/note instead of Local_Theory.notes/note *)
        val (((((psimps', [pinducts']), [termination']), cases'), pelims'), lthy2) =
          lthy1
          |> addsmps (concealed_partial o Binding.qualify false "partial")
               "psimps" concealed_partial psimp_attribs psimps
          ||>> Proof_Local_Lthy.notes [((concealed_partial (derived_name defname "pinduct"), []),
                simple_pinducts |> map (fn th =>
                 let val th' = Thm.forall_elim_vars 0 th
                 in ([th'],
                 [Attrib.case_names cnames, Attrib.consumes (1 - Thm.nprems_of th')] @
                 @{attributes [induct pred]}) end))]
          ||>> (apfst snd o
            Proof_Local_Lthy.note
              ((Binding.concealed (derived_name defname "termination"), []), [termination]))
          ||>> fold_map (note_derived ("cases", [Attrib.case_names cnames]))
            (fnames ~~ map single cases)
          ||>> fold_map (note_derived ("pelims", [Attrib.consumes 1, Attrib.constraints 1]))
            (fnames ~~ pelims)
          ||> (case domintros of NONE => I | SOME thms =>
                Proof_Local_Lthy.note ((derived_name defname "domintros", []), thms) #> snd)

        val info =
          { add_simps=addsmps, fnames=fnames, case_names=cnames, psimps=psimps',
          pinducts=snd pinducts', simps=NONE, inducts=NONE, termination=termination', totality=NONE,
          fs=fs, R=R, dom=dom, defname=defname, is_partial=true, cases=flat cases',
          pelims=pelims',elims=NONE}

        val _ =
          Proof_Display.print_consts do_print (Position.thread_data ()) lthy2
            (K false) (map fst fixes)
      in
        (* Proof-local: use Context.proof_map for declaration instead of Local_Theory.declaration *)
        (info,
         lthy2 |> Context.proof_map
           (add_function_data (transform_function_data Morphism.identity info)))
      end
  in
    ((goal_state, afterqed), lthy')
  end

fun gen_add_function do_print prep fixspec eqns config tac lthy =
  let
    val ((goal_state, afterqed), lthy') =
      prepare_function_top do_print prep fixspec eqns config lthy
    val pattern_thm =
      case SINGLE (tac lthy') goal_state of
        NONE => error "pattern completeness and compatibility proof failed"
      | SOME st => Goal.finish lthy' st
  in
    lthy'
    |> afterqed [[pattern_thm]]
  end

fun add_function_local a b c d = gen_add_function false Specification.check_multi_specs a b c d
fun add_function_cmd_local a b c d int = gen_add_function int Specification.read_multi_specs a b c d


(* ===== Adapted from function.ML: termination ===== *)

fun prepare_termination_proof_local prep_binding prep_term raw_term_opt lthy =
  let
    val term_opt = Option.map (prep_term lthy) raw_term_opt
    val info =
      (case term_opt of
        SOME t =>
          (case import_function_data t lthy of
            SOME info => info
          | NONE => error ("Not a function: " ^ quote (Syntax.string_of_term lthy t)))
      | NONE =>
          (case import_last_function lthy of
            SOME info => info
          | NONE => error "Not a function"))

    val { termination, fs, R, add_simps=info_add_simps, case_names, psimps,
      pinducts, defname, fnames, cases, dom, pelims, ...} = info
    val domT = domain_type (fastype_of R)
    val goal = HOLogic.mk_Trueprop (HOLogic.mk_all ("x", domT, mk_acc domT R $ Free ("x", domT)))
    fun afterqed [[raw_totality]] lthy1 =
      let
        val totality = Thm.close_derivation \<^here> raw_totality
        val remove_domain_condition =
          full_simplify (put_simpset HOL_basic_ss lthy1
            addsimps [totality, @{thm True_implies_equals}])
        val tsimps = map remove_domain_condition psimps
        val tinduct = map remove_domain_condition pinducts
        val telims = map (map remove_domain_condition) pelims
      in
        lthy1
        (* Proof-local: use info_add_simps from the info record (already uses Proof_Local_Lthy.note) *)
        |> info_add_simps prep_binding "simps" prep_binding simp_attribs tsimps
        (* Proof-local: skip Code.declare_default_eqns (requires local theory) *)
        ||>> Proof_Local_Lthy.note
          ((prep_binding (derived_name defname "induct"), [Attrib.case_names case_names]), tinduct)
        ||>> fold_map (note_derived ("elims", [Attrib.consumes 1, Attrib.constraints 1]))
          (map prep_binding fnames ~~ telims)
        |-> (fn ((simps,(_,inducts)), elims) => fn lthy2 =>
          let val info' = { is_partial=false, defname=defname, fnames=fnames, add_simps=info_add_simps,
            case_names=case_names, fs=fs, R=R, dom=dom, psimps=psimps, pinducts=pinducts,
            simps=SOME simps, inducts=SOME inducts, termination=termination, totality=SOME totality,
            cases=cases, pelims=pelims, elims=SOME elims}
            |> transform_function_data (Morphism.binding_morphism "" prep_binding)
          in
            (info',
             lthy2
             (* Proof-local: use Context.proof_map for declaration *)
             |> Context.proof_map
                  (add_function_data (transform_function_data Morphism.identity info'))
             (* Proof-local: skip Spec_Rules.add (requires local theory) *))
          end)
      end
  in
    (goal, afterqed, termination)
  end

fun prove_termination_local raw_term_opt tac lthy =
  let
    val (goal, afterqed, termination) =
      prepare_termination_proof_local I Syntax.check_term raw_term_opt lthy

    val totality = Goal.prove lthy [] [] goal (K tac)
  in
    afterqed [[totality]] lthy
  end


(* ===== Adapted from fun.ML ===== *)

(* Phase 1 primitive. Runs prepare_function_top to get the pat-completeness
   goal state + afterqed continuation, and wraps the continuation so it
   returns the Proof.context only (dropping the info record). *)
fun prepare_pat_goal fixes specs config int ctxt =
  let
    val ((goal_state, raw_afterqed), lthy') =
      prepare_function_top int Specification.read_multi_specs fixes specs config ctxt
    fun pat_afterqed pats ctxt0 = snd (raw_afterqed pats ctxt0)
  in
    {pat_goal_state = goal_state,
     pat_afterqed = pat_afterqed,
     lthy_after_prepare = lthy'}
  end

(* Phase 2 primitive. Calls prepare_termination_proof_local to build the
   termination proposition and a continuation, wrapping the continuation
   so it returns the Proof.context only. *)
fun prepare_term_goal lthy =
  let
    val (goal, raw_afterqed, _) =
      prepare_termination_proof_local I Syntax.check_term NONE lthy
    fun term_afterqed totalities ctxt0 = snd (raw_afterqed totalities ctxt0)
  in
    {term_goal = goal, term_afterqed = term_afterqed}
  end


(* ===== Entry point ===== *)

(* Fully-automatic convenience wrapper: runs both phases with the default
   tactics and returns the resulting proof context. Preserves the
   behaviour of the pre-split implementation. *)
fun add_fun_cmd fixes specs config int outer_ctxt =
  let
    val ctxt = Variable.set_body false outer_ctxt
    val {pat_goal_state, pat_afterqed, lthy_after_prepare} =
      prepare_pat_goal fixes specs config int ctxt
    val pat_thm =
      (case SINGLE (Pat_Completeness.pat_completeness_tac lthy_after_prepare 1
                      THEN auto_tac lthy_after_prepare) pat_goal_state of
         NONE => error "pattern completeness and compatibility proof failed"
       | SOME st => Goal.finish lthy_after_prepare st)
    val lthy_after_partial = pat_afterqed [[pat_thm]] lthy_after_prepare
    val {term_goal, term_afterqed} = prepare_term_goal lthy_after_partial
    val {termination, ...} =
      (case Function_Common.import_last_function lthy_after_partial of
         SOME info => info
       | NONE => error "prove_termination: no function data")
    val termination' = Thm.forall_elim_vars 0 termination
    val default_tac =
      resolve_tac lthy_after_partial [termination'] 1 THEN
      Function_Common.termination_prover_tac false lthy_after_partial
    val totality =
      Goal.prove lthy_after_partial [] [] term_goal (K default_tac)
    val lthy_final = term_afterqed [[totality]] lthy_after_partial
  in
    Variable.restore_body outer_ctxt lthy_final
  end

end
