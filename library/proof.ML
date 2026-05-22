signature MINILANG = sig

type stack
type state
type operation = state -> state
type command = operation parser

type variables = (string * typ) list
type local_facts = (string * term) list
type items = variables * local_facts
type fact = Facts.ref * Token.src list

val context_of  : state -> Proof.context
val leading_proof_sequent_of : state -> thm
val equiv_proof_state : state * state -> bool
val num_goals   : state -> int
val goals_of'   : thm -> term list  (* extract the list of subgoal terms
                                       from a (possibly-protected) proof
                                       state theorem — walks through the
                                       nested `HOL.GOAL` wrappers that
                                       `protect_goals` produces, whereas
                                       `Thm.prems_of` would stop at the
                                       outer `Pure.imp` chain *)
val leading_goal_data : state -> (items * term) option * int
val map_context : (Proof.context -> Proof.context) -> state -> state
val schematic_vars_of_leading_goal : state -> (indexname * typ) list

datatype fail_reason = INVALID_OPR | PROOF_FAIL | TERMLANG
exception OPR_FAIL of fail_reason * string

type with_clause = (bool (*with or without*) * string (*name*) * thm) list
type opt_var_names  = string option list option
type opt_prem_names = string option list option

(* options *)

val atomize_goals_in_printing : bool Config.T
val working_mode : string Config.T
val mini_single_cmd_timeout : int Config.T
val typ_parsing_mode : string Config.T
val install_relaxed_typ_parsing : Context.generic -> Context.generic
val high_auto_mode : bool Config.T
val transparent_intro : bool Config.T
    (*If enabled, no INTRO command is required. All premises and universal variables in proof goals
      will be introduced (i.e., moved into the meta) transparently:
      1. All premises and universal variables in proof goals are always displayed as meta
         facts / variables.
      2. MiniLang determines the appropriate time to introduce the premises and the variables.
         This time is the moment before command HAVE and CONSIDER happen.*)
val mini_use_improved_SH : bool Config.T
val strict_end: bool Config.T
    (*If enabled, the NEXT and END will not apply SH but require the proof goals are all solved*)
val counter_mode : string Config.T
val INTRO_split_prem_conj : bool Config.T
val INTRO_split_prem_conj_size_limit : int Config.T
val INTRO_mk_block : bool Config.T
val auto_deconflict_bound : bool Config.T
val deconflict_case_fixes : bool Config.T
val auto_calculation : bool Config.T
val induct_auto_insert_facts : bool Config.T
val consumes_policy : string Config.T

val chk_working_mode : string -> unit

(* Bound name deconfliction *)

val deconflict_bound_names : term -> term
val deconflict_bound_names_thm : thm -> thm

(* Operations *)

val INIT : Proof.context -> thm -> state
val INIT': Proof.state -> state
val conclude : Proof.context -> state -> thm
val is_finished : state -> bool
val ready_to_finish : state -> bool

(*Thread local*)
datatype message = New_Items of items
                 | Goals     of term list
                 | Consider_Case of string * items
                 | Newly_Fixed of (string * typ) list (*external_name * raw type*)
                 | Internal of exn
val set_reporter : (message (*new items*) -> unit) -> unit
val get_reporter : unit -> (message (*new items*) -> unit)

val empty_items : items
val cat_items : items -> items -> items
val get_local_facts : state -> local_facts

datatype intros_mode = ALL_SUBGOALS | SINGLE_GOAL
val INTRO : intros_mode -> bool option
         -> opt_var_names -> opt_prem_names
         -> state -> items * state
val INTRO_CMD : command
val TRANSPARENT_INTRO : operation

val is_conj_goal : thm -> bool
val SPLIT_CONJS : operation
val SPLIT_CONJS_CMD : command

(* Helper functions for INTRO *)
val need_intro : thm -> bool
val strip_meta_and_hol_hhf : term -> (string * typ) list * term list * term
val deep_destruct_prem : Proof.context -> thm -> thm list
val deep_destruct_term : Proof.context -> term -> term list

val apply : string -> context_tactic -> Time.time option -> stack -> stack
val apply_method : string -> thm list -> Method.method -> Time.time option -> stack -> stack
val APPLY   : Time.time option -> thm list -> Method.text -> operation
val APPLY'' : Time.time option -> fact list -> Method.text -> operation
val APPLY_CMD : command

val crush_timeout : int Config.T
val CRUSH : opt_var_names * with_clause -> operation
val CRUSH_CMD : command
val SIMP : with_clause -> operation
val SIMP'' : (bool * (Facts.ref * Token.src list)) list -> operation
val SIMP_CMD : command

val SIMPLIFY_GOAL_AND_PREMISES : thm list -> simproc list -> bool -> string list -> bool
        -> (term list -> string list) option
        -> ((string * typ) list -> string list) option
        -> Time.time option
        -> state -> items * state
val SIMPLIFY_GOAL_AND_PREMISES'' : fact list -> bool -> string list -> bool -> operation
val SIMPLIFY_CMD : command

val potential_defs_of_const : Proof.context -> string -> (string * thm) list

val UNFOLD : thm list -> operation
val UNFOLD_CMD : command

(* INDUCT facts are split into two roles:
 *   using     : facts intended to discharge the rule's major premises
 *               (the `consumes` count). Required: |using| >= consumes.
 *               When `strict_consumes_check` is true, also |using| <= consumes.
 *   insertion : named facts to be wrapped with HOL.TAG + conjI, inserted
 *               as a goal premise via a dedicated `Method.insert_tac`
 *               call (NOT via `induction_tac`'s `facts` parameter, so
 *               `Rule_Cases.consume` never touches them), and restored
 *               in each case's context under their original name by
 *               `update_tampered`. Each entry is (name, thm list) —
 *               matching Isabelle's multi-thm fact shape. Auto-insert
 *               populates this from the context scan; agent
 *               `facts_to_generalize` populates it from explicit names;
 *               the two sources are merged in INDUCT' with explicit
 *               entries overriding same-named auto entries. *)
type induct_facts = {using: thm list, insertion: (string * thm list) list}

val INDUCT : bool * ((binding option * (term * bool)) option list list *
              (((string * typ) list list * term option list) * thm list option))
          -> opt_var_names
          -> induct_facts
          -> operation
val INDUCT'' : Token.src * opt_var_names * fact list -> operation
val INDUCT_CMD : command

(* CASE_SPLIT only takes `using` facts — no insertion slot. (If a case
 * analysis ever needs a named-facts TAG channel like INDUCT's, follow
 * the INDUCT' pattern rather than reinstating `using @ insertion`,
 * which is unsafe because `Rule_Cases.consume` would swallow the
 * insertion tail.) *)
val CASE_SPLIT   : bool * (term option list list * thm option)
                -> opt_var_names
                -> thm list
                -> operation
val CASE_SPLIT'' : Token.src * opt_var_names * fact list -> operation
val CASE_SPLIT_CMD : command

(* Analysis of an INDUCT / CASE_SPLIT invocation without executing the tactic.
 * Reports the picked rule and the premise shapes the user's `using` facts
 * must match to discharge the rule's `consumes` major premises.
 *
 * `consume_premises` is the list of the first `consumes` premises of the
 * post-inst_rule theorem — exactly what Rule_Cases.consume will try to
 * unify against user-supplied facts (via Drule.multi_resolve). *)
type induct_analysis =
  {rule: thm,
   rule_name: string option,
   consumes: int,
   consume_premises: term list,
   remaining_premises: term list}

val analyze_induct : Proof.context
  -> bool * ((binding option * (term * bool)) option list list *
             (((string * typ) list list * term option list) * thm list option))
  -> thm list
  -> induct_analysis option
val analyze_case_split : Proof.context
  -> bool * (term option list list * thm option)
  -> thm list
  -> induct_analysis option

val record_history : string -> operation
val restore_history : string -> operation

val HAVE : (binding * string option * mixfix) list
        -> (Attrib.binding * (string * string list) list) list
        -> (Attrib.binding * (string * string list) list) list
        -> operation
val HAVE'' : (binding * typ option * mixfix) list
        -> (Attrib.binding * (term * term list) list) list
        -> (Attrib.binding * (term * term list) list) list
        -> operation
val HAVE_CMD : command

val SUFFICES : (binding * string option * mixfix) list
    -> (Attrib.binding * (string * string list) list) list
    -> (Attrib.binding * (string * string list) list) list
    -> operation
val SUFFICES'' : (binding * typ option * mixfix) list
    -> (Attrib.binding * (term * term list) list) list
    -> (Attrib.binding * (term * term list) list) list
    -> operation
val SUFFICES_CMD : command

val INST_VAR : (indexname * string) list -> operation
val INST_VAR'' : (indexname * term) list -> operation
val INST_VAR_CMD : command

val SPECIALIZE   : string option -> fact list -> (Minilang_Aux.var_name * string) list -> fact list -> operation
val SPECIALIZE'' : string option -> thm list  -> (Minilang_Aux.var_name * term) list   -> thm list  -> operation
val SPECIALIZE_CMD : command

val CONSIDER : (
               (binding * string option * mixfix) list
             * ( (binding * string option * mixfix) list
               * (string * string list) list list
               * (Attrib.binding * (string * string list) list) list )
             ) list
          -> operation
val CONSIDER_CMD : command

val HAMMER : (string option -> Proof.context -> thm -> string * thm) -> operation
val HAMMER_CMD : command
val enable_cache_by_step : bool Config.T
val default_prover : Time.time option -> Sledgehammer.fact_override -> Proof.context
                  -> string option -> Proof.context -> thm -> string * thm

val END : Sledgehammer.fact_override -> operation
val END_CMD : command
datatype endblk_type = T_END | T_NXT
val type_of_end : state -> endblk_type option

val NOTATION   : Syntax.mode -> (term * mixfix) list -> operation
val NOTATION'' : Syntax.mode -> (string * mixfix) list -> operation
val NOTATION_CMD : command

val NXT : opt_var_names -> Sledgehammer.fact_override -> operation
val NXT_CMD : command
val END_or_NXT : opt_var_names -> Sledgehammer.fact_override -> operation

val END_or_NXT_by_SORRY : opt_var_names -> state -> state
val END_or_NXT_by_SORRY_CMD : command

(* SORRY_NEXT: cheat the current subgoal in the current HHF. If the HHF
   still has remaining subgoals afterwards (the common multi-goal case),
   return the state with one fewer goal. If the HHF becomes empty and
   an ENDBLK T_NXT is next, pop it + invoke the MAGIC next-callback.
   Errors if the HHF becomes empty over an ENDBLK T_END — in that case
   SORRY_END_ALL is the right command. *)
val SORRY_NEXT : opt_var_names -> state -> state
val SORRY_NEXT_CMD : command

(* SORRY_END_ALL: cheat every remaining subgoal in the current HHF,
   then pop the enclosing ENDBLK. Used to discard an entire (possibly
   multi-goal) block after a recovery failure. Unlike `SORRY` /
   `SORRY_NEXT`, this closes the whole block regardless of how many
   residuals remain — so `Define`'s deferred pat-completeness /
   termination block (with 2+ unsolved residuals after a body failure)
   can be closed in one operation. *)
val SORRY_END_ALL : opt_var_names -> state -> state
val SORRY_END_ALL_CMD : command

(* SORRY_ONLY: cheat the current subgoal in the current HHF without
   any NEXT or END transition. The stack frame stays in place — the
   ENDBLK (if any) is left untouched. This is the sorry analogue of
   HAMMER: resolve one goal, stay put. Used by the AoA driver to
   skip-proof the last GoalNode child whose resulting_state feeds
   directly into the parent's _state_before_ending_. *)
val SORRY_ONLY : operation
val SORRY_ONLY_CMD : command

val LET   : (term list * term) list -> operation
val LET'' : (string list * string) list -> operation
val LET_CMD : command

datatype tree = PROP  of items * term (*goal*)
              | BUNDL of items * tree list
              | BLOCK of tree
val print_state : state -> tree
val atomize_tree : Proof.context -> tree -> tree
val context_of_leading_goal : tree -> items * term (*goal*)
val PRINT : operation
val PRINT_CMD : command

val OPEN_MODULE   : Expression.expression_i -> state -> state
val OPEN_MODULE'' : Expression.expression   -> state -> state
val OPEN_MODULE_CMD : Token.T list -> (state -> state) * Token.T list

datatype config = CFG_NOTE   of Thm.binding * (thm list * attribute list) list
                | CFG_BUNDLE of Bundle.name
val CONFIG : config list -> operation
val CONFIG_FACTS'' : (Attrib.binding * (Facts.ref * Token.src list) list) list -> operation
val CONFIG_BUNDL'' : string list -> operation

val CONFIG_CMD : command

val RULE : (Facts.ref * Token.src list) list (*rule*)
        -> (Facts.ref * Token.src list) list (*with facts*)
        -> operation
val RULE_CMD : command

val CHOOSE : term list -> operation
val CHOOSE'' : (string * (binding * string option * mixfix) list) list -> operation
val CHOOSE_CMD : command

val DEFINE : (binding * typ option * mixfix) list
          -> (Thm.binding * (term * term list) list) list
          -> (binding * typ option * mixfix) list
          -> operation
val DEFINE'' : (binding * string option * mixfix) list
            -> (Attrib.binding * (string * string list) list) list
            -> (binding * string option * mixfix) list
            -> operation
val DEFINE_CMD : command

val FUN'' : (binding * string option * mixfix) list
         -> Specification.multi_specs_cmd
         -> {metric: string list, open_on_fail: bool}
         -> operation
val FUN_CMD : command
val FUN_DEBUG_CMD : command

(* Create simprocs that fire only on specific target terms.
   Unlike thms_to_once_simprocs, these fire on ALL indicated targets, not just once.
   Each (thm, targets) pair produces simprocs whose proc checks aconv against targets. *)
val thms_to_targeted_simprocs : Proof.context -> (thm * term list) list -> simproc list

(* After a function definition, check its .simps for looping rules and
   remove them from the simpset. The function stays defined and its
   .simps remain accessible by name. *)
val remove_looping_simps : Proof.context -> Proof.context
val fun_fake_automatic_failure : bool Config.T
val fun_fake_pat_completeness_failure : bool Config.T

val STEP   : fact list ->  term  -> operation
val STEP'' : fact list -> string -> operation
val STEP_CMD : command

val CHAINING : string option -> thm list -> operation
val CHAINING_CMD : command

val COMPUTE : string -> term -> operation

(* Toplevel *)

val lex_cmds : string -> Token.src list
val parse_cmds : Token.src list -> operation
val PROVE : operation -> Proof.context -> thm -> thm

val METHOD : string -> Method.method
val MP : Proof.context -> thm -> thm -> thm

(* Internal *)

exception IH_MAP of (string * string list) list
exception SH_PRF of string
exception REPLACE_CMD of string * string

(* Reporter signals fired by FUN / FUN_DEBUG / FUN'' when a residual
   pat-completeness or termination goal gets deferred onto the
   minilang stack for interactive discharge. Exposed here so
   downstream (e.g. the Agent's message packer) can pattern-match
   on them. *)
exception PAT_COMPLETENESS_PROOF_OPENED
exception TERMINATION_PROOF_OPENED
exception DROPPED_INSERTION_FACTS of string list

end

structure Minilang : MINILANG = struct
open Minilang_Aux

(** Preliminaries **)

val assm_N = "assm"
fun assm_name i = assm_N ^ string_of_int i

(* options *)

val atomize_goals_in_printing = Attrib.setup_config_bool \<^binding>\<open>min_shell_atomize_goals\<close> (K true)
val working_mode = Attrib.setup_config_string \<^binding>\<open>working_mode\<close> (K "RELAXED")
val transparent_intro = Attrib.setup_config_bool \<^binding>\<open>transparent_intro\<close> (K false)
val high_auto_mode = Attrib.setup_config_bool \<^binding>\<open>high_auto_mode\<close> (K false)
val strict_end = Config.declare_bool ("Minilang.strict_end", \<^here>) (K false)
val counter_mode = Config.declare_string ("Minilang.counter_mode", \<^here>) (K "consecutive")
val INTRO_split_prem_conj = Config.declare_bool ("Minilang.INTRO_split_prem_conj", \<^here>) (K true)
val INTRO_split_prem_conj_size_limit = Config.declare_int ("Minilang.INTRO_split_prem_conj_size_limit", \<^here>) (K 20)
val INTRO_mk_block   = Config.declare_bool ("Minilang.INTRO_mk_block", \<^here>) (K false)
val auto_deconflict_bound = Config.declare_bool ("Minilang.auto_deconflict_bound", \<^here>) (K false)
val deconflict_case_fixes = Config.declare_bool ("Minilang.deconflict_case_fixes", \<^here>) (K false)
val auto_calculation = Config.declare_bool ("Minilang.auto_calculation", \<^here>) (K true)

fun chk_working_mode mode =
      if member (op =) ["RELAXED", "COMPLETE_NEXT", "STRICT"] mode
      then ()
      else error "working_mode must be either STRICT, RELAXED or COMPLETE_NEXT"

(* Deconflict bound variable names in a term to avoid shadowing.
   Always uses Variable.names_of ctxt as base to avoid conflicts with context names.
*)
val deconflict_bound_names = Minilang_Aux.deconflict_bound_names

fun deconflict_bound_names_thm thm =
  let val prop = Thm.prop_of thm
      val prop' = deconflict_bound_names prop
   in if prop aconv prop' then thm
      else Thm.renamed_prop prop' thm
  end


type variables = (string * typ) list
type local_facts = (string * term) list
type items = variables * local_facts
type fact = Facts.ref * Token.src list
type has_introduced = bool

val empty_items : items = ([],[])
fun join_lstR pr = AList.join (op =) (fn _ => fn (_,x) => x) pr
fun join_lstL pr = AList.join (op =) (fn _ => fn (x,_) => x) pr

(*primary is the newer. The newer is appended to the list*)
fun cat_items (vs',hs') (vs,hs)
      = (join_lstR (vs', vs), join_lstL (hs', hs))

(*only for printing*)
datatype tree = PROP  of items * term (*goal*)
              | BUNDL of items * tree list
              | BLOCK of tree
type param = exn
datatype endblk_type = T_END | T_NXT
datatype frame = HHF   of thm (*a local_facts bundle node, represented as a Hereditary Harrop Formula*)
                        * items
               | MAGIC of (Proof.context -> thm * items * frame list * param -> Proof.context * frame list)
                        * (param -> tree -> tree)
                        * param
               | ENDBLK of endblk_type

type opt_var_names  = string option list option
type opt_prem_names = string option list option
exception NO_PARAM
exception CASE_NAME of opt_var_names

(* Emitted when FUN leaves a residual pat-completeness goal on the minilang
   stack for the user to discharge interactively (only reachable via the
   ML-level FUN'' API with open_on_fail = true). *)
exception PAT_COMPLETENESS_PROOF_OPENED

(* Emitted when FUN leaves a residual termination goal on the minilang
   stack (only reachable via the ML-level FUN'' API with open_on_fail
   = true). *)
exception TERMINATION_PROOF_OPENED

exception DROPPED_INSERTION_FACTS of string list

type stack = Proof.context * (frame list)
  (*invariant: the head must be an HHF*)

type state = stack              (*current stack*)
           * stack Symtab.table (*history*)
           * int                (*cache id*)

type operation = state -> state
type command = operation parser

fun context_of (((ctxt,_), _, _) : state) = ctxt
fun leading_proof_sequent_of (((_, HHF (seq, _) :: _), _, _) : state) = seq
(*only checks state sequent*)
fun equiv_proof_state ( ((ctxt, HHF (st, _) :: _), _, _) , ((_, HHF (st', _) :: _), _, _) )
      = Thm.equiv_thm (Proof_Context.theory_of ctxt) (st, st')
fun map_context F ((ctxt,SK), his, ID) = ((F ctxt,SK), his, ID)

fun get_local_facts (((_, SK), _, _): state) : local_facts =
  case SK of
      (HHF (_, (_, facts)) :: _) => facts
    | _ => []

exception BROKEN_INVARIANT

datatype fail_reason = INVALID_OPR | PROOF_FAIL | TERMLANG
exception OPR_FAIL of fail_reason * string

(* Helpers *)

fun is_protected (\<^Const>\<open>Pure.prop\<close> $ _) = true
  | is_protected (\<^Const>\<open>Pure.imp\<close> $ _ $ X) = is_protected X
  | is_protected (\<^Const>\<open>Pure.all _\<close> $ Abs (_,_, X)) = is_protected X
  | is_protected _ = false

fun mk_binding long_name =
  let val names = Long_Name.explode long_name
      fun mk [] = error "BUG"
        | mk [x] = Binding.name x
        | mk (q::L) = Binding.qualify_name true (mk L) q
   in case names
   of "local"::L => mk L
    | L => mk L
  end

fun protect_goals th =
  let fun conv ctm =
        case Thm.term_of ctm
          of Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X =>
            (case X
               of Const(\<^const_name>\<open>Pure.prop\<close>, _) $ _ => Conv.all_conv ctm
                | Const(\<^const_name>\<open>HOL.GOAL\<close>, _) $ _ => Conv.all_conv ctm
                | _ => (Conv.arg_conv (conv then_conv 
                                       Conv.rewr_conv Thms.GOAL_def'sym)) ctm)
           | _ => Conv.all_conv ctm
   in Conv.fconv_rule conv th
  end

fun pop_n_goals n th =
  let open Conv
      fun conv N ctm =
        if N <= 1 then all_conv ctm
        else case Thm.term_of ctm
          of Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _
                $ (Const(\<^const_name>\<open>HOL.GOAL\<close>, _) $ _ ) =>
             (arg_conv (rewr_conv Thms.GOAL_def) then_conv
              arg_conv (conv (N-1)) then_conv
              rewr_conv Thms.conjunction_imp'sym) ctm
           | _ => raise THM ("pop_n_goals: insufficient goals", n, [th])
   in if n <= 1 then th else fconv_rule (conv n) th
  end

fun init_goal ctxt th = th
      |> Conv.fconv_rule (concl_conv iso_atomize ctxt)
      |> protect_goals

val num_goals_of =
  let fun calc ret (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ (Const(\<^const_name>\<open>HOL.GOAL\<close>, _) $ X))
            = calc (ret+1) X
        | calc ret (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ (Const(\<^const_name>\<open>Pure.prop\<close>, _) $ _)) = ret + 1
        | calc ret (Const(\<^const_name>\<open>HOL.GOAL\<close>, _) $ X) = calc (ret+1) X
        | calc _ _ = raise BROKEN_INVARIANT
   in fn Const (\<^const_name>\<open>Pure.prop\<close>, _) $ _ => 0
       | tm => calc 0 tm
  end
val num_goals_of' = num_goals_of o Thm.prop_of
fun num_goals ((_, HHF (st, _) :: _), _, _) = num_goals_of' st
  | num_goals _ = raise BROKEN_INVARIANT

fun no_goal (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ (Const(\<^const_name>\<open>HOL.GOAL\<close>, _) $ _)) = false
  | no_goal (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ (Const(\<^const_name>\<open>Pure.prop\<close>, _) $ _)) = false
  | no_goal (Const(\<^const_name>\<open>HOL.GOAL\<close>, _) $ _) = false
  | no_goal _ = true
val no_goal' = no_goal o Thm.prop_of

fun no_subgoal (Const(\<^const_name>\<open>Pure.prop\<close>, _) $ _) = true
  | no_subgoal (Const(\<^const_name>\<open>HOL.GOAL\<close>, _) $ _) = true
  | no_subgoal _ = false
val no_subgoal' = no_subgoal o Thm.prop_of

val goals_of =
  let fun collect (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ G $ (Const(\<^const_name>\<open>HOL.GOAL\<close>, _) $ X))
            = G :: collect X
        | collect (Const(\<^const_name>\<open>HOL.GOAL\<close>, _) $ X)
            = \<^prop>\<open>True\<close> :: collect X
        | collect (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ G $ (Const(\<^const_name>\<open>Pure.prop\<close>, _) $ _))
            = [G]
        | collect _ = raise BROKEN_INVARIANT
   in fn Const (\<^const_name>\<open>Pure.prop\<close>, _) $ _ => [\<^prop>\<open>True\<close>]
       | tm => collect tm
  end
val goals_of' = goals_of o Thm.prop_of

(* Extract (leading_goal_items * leading_goal_term, goals_count) from a state.
   Returns (NONE, 0) for solved / empty states.  Used by the agent RPC
   packer as a flat replacement for the full `print_state` tree. *)
fun leading_goal_data ((_, SK), _, _) =
      (case SK of
         HHF (st, items) :: _ =>
           if no_goal' st then (NONE, 0)
           else (SOME (items, hd (goals_of' st)), num_goals_of' st)
       | _ => (NONE, 0))

(* Extract all schematic variables from the leading proof goal *)
fun schematic_vars_of_leading_goal ((_, HHF (st, _) :: _), _, _) =
  let
    (* Get the first goal from the HHF sequent *)
    val goals = goals_of' st
    val goal = case goals of
                 [] => \<^prop>\<open>True\<close>  (* No goals, return True *)
               | (g :: _) => g

    (* Collect all Vars from the goal term using Term.add_vars *)
    val vars = Term.add_vars goal []
   in vars |> distinct (op =)
  end
  | schematic_vars_of_leading_goal _ = raise BROKEN_INVARIANT

fun concl_of (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ (Const(\<^const_name>\<open>HOL.GOAL\<close>, _) $ X)) = concl_of X
  | concl_of (Const(\<^const_name>\<open>HOL.GOAL\<close>, _) $ X) = concl_of X
  | concl_of (Const(\<^const_name>\<open>Pure.prop\<close>, _) $ X) = X
  | concl_of (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ (Const(\<^const_name>\<open>Pure.prop\<close>, _) $ X)) = X
  | concl_of _ = raise BROKEN_INVARIANT
  

fun conclude_goal th =
  let fun conv ctm =
        (case Thm.term_of ctm
           of Const(\<^const_name>\<open>HOL.GOAL\<close>, _) $ _ => Conv.rewr_conv Thms.GOAL_def ctm
            | Const(\<^const_name>\<open>Pure.prop\<close>, _) $ _ => Conv.all_conv ctm
            | _ => raise THM ("conclude_goal", 0, [th]))
   in Conv.fconv_rule conv th
  end

fun finalize_goal ctxt th = th
      |> Conv.fconv_rule (concl_conv iso_rulify ctxt)

(* Printer *)

val SOLVED_TREE = BUNDL (empty_items, [])

fun print_stack [] = SOLVED_TREE
  | print_stack (S::L) =
      let 
          fun prt t [] = t
            | prt t (HHF (st, items) :: L) =
                let val goals = case goals_of' st
                                  of [] => raise BROKEN_INVARIANT
                                   | (_::prems) => prems
    
                    val nodes = map (fn goal => PROP (([],[]), goal)) goals
                 in prt (BUNDL (items, t::nodes)) L
                end
            | prt t (MAGIC (_, PRT, param) :: L) = prt (PRT param t) L
            | prt t (ENDBLK _ :: L) = prt t L
          fun prt0 (HHF (st, items)) =
              if no_goal' st
              then SOLVED_TREE
              else(case goals_of' st
                   of [goal] => PROP (items, goal)
                    | [] => raise BROKEN_INVARIANT
                    | goals => BUNDL (items, map (PROP o pair empty_items) goals) )
            | prt0 _ = raise BROKEN_INVARIANT
       in prt (prt0 S) L
      end

fun print_state ((_,SK),_,_) = print_stack SK

fun cat_tree (PROP (items, goal)) (PROP (items', _)) = PROP (cat_items items items', goal)
  | cat_tree (BUNDL (items, goal)) (PROP (items', _)) = BUNDL (cat_items items items', goal)
  | cat_tree T (BUNDL (items', goals)) = BUNDL (items', cat_tree T (hd goals) :: tl goals)
  | cat_tree (BLOCK T) U = BLOCK (cat_tree T U)
  | cat_tree T (BLOCK U) = BLOCK (cat_tree T U)

fun atomize_tree ctxt (PROP (items, goal)) = PROP (items, Object_Logic.atomize_term ctxt goal)
  | atomize_tree ctxt (BUNDL (items, goal)) = BUNDL (items, map (atomize_tree ctxt) goal)
  | atomize_tree ctxt (BLOCK tree) = BLOCK (atomize_tree ctxt tree)

(* fun fake_intro_ctxt ctxt *)

val context_of_leading_goal =
  let fun collect V F (PROP  ((V',F'),term)) = ((V @ V', F @ F'), term)
        | collect V F (BUNDL ((V',F'),[]))   = ((V @ V', F @ F'), \<^prop>\<open>True\<close>)
        | collect V F (BUNDL ((V',F'),chil)) = collect (V @ V') (F @ F') (hd chil)
        | collect V F (BLOCK tree) = collect V F tree
   in collect [] []
  end

fun fold_all_names f (PROP ((V,F),_)) x =
      x |> fold (f o fst) V |> fold (f o fst) F
  | fold_all_names f (BUNDL ((V,F), chil)) x =
      x |> fold (f o fst) V |> fold (f o fst) F
        |> fold (fold_all_names f) chil
  | fold_all_names f (BLOCK tree) x = fold_all_names f tree x

fun quanlifiers_of tree =
  let fun merge [] L = L
        | merge [_] L = L
        | merge (h::L') L = merge L' (insert (op =) h L)
   in fold_all_names (merge o Long_Name.explode) tree []
  end

(* Common Syntax *)

type with_clause = (bool (*with or without*) * string (*name*) * thm) list

val WITH_CLAUSE    = Parse.$$$ "WITH"    |-- Scan.repeat Parse.thm
val WITHOUT_CLAUSE = Parse.$$$ "WITHOUT" |-- Scan.repeat Parse.thm
val with_parser =
        Scan.repeat ( WITH_CLAUSE    >> pair true
                   || WITHOUT_CLAUSE >> pair false )
     >> maps (uncurry (map o pair))

val orverride_parser =
        Scan.repeat (   (Parse.$$$ "WITH"    |-- Scan.repeat Parse.thm >> rpair [])
                     || (Parse.$$$ "WITHOUT" |-- Scan.repeat Parse.thm >>  pair []) )
     >> (fn LL => fold_rev (fn (A,D) => fn (A',D') => (A @ A', D @ D') ) LL ([],[])
               |> (fn (A,D) => {add = A, del = D, only = false}))

fun name_of_ref (Facts.Named ((name,_), _)) = name
  | name_of_ref (Facts.Fact _) = ""

fun read_with ctxt with_lems =
      maps (fn (flag, fact) =>
        let val name = name_of_ref (fst fact)
         in Attrib.eval_thms ctxt [fact]
         |> map (fn th => (flag, name, th) )
        end ) with_lems

fun apply_WITH with_lems =
  fold (fn (flag, name, thm) =>
    Context.proof_map (Phi_Sledgehammer_Solver.with_rule flag name thm)) with_lems

fun stack_is_finished (_, [HHF (st', _)]) = no_goal' st'
  | stack_is_finished _ = false
fun is_finished (SK,_,_) = stack_is_finished SK

(* The current (top) block's goal is closed.  Used by `chk_block_end` so that
   END/NEXT in strict mode only require the *local* block to be done — not the
   entire proof stack. *)
fun stack_top_finished (_, HHF (st, _) :: _) = no_goal' st
  | stack_top_finished _ = false
fun stack_top_no_subgoal (_, HHF (st, _) :: _) = no_subgoal' st
  | stack_top_no_subgoal _ = false

fun stack_is_ready_to_finish (_, HHF (st, _) :: _) = Thm.no_prems st
  | stack_is_ready_to_finish _ = raise BROKEN_INVARIANT
fun ready_to_finish (s as (SK,_,_)) = stack_is_ready_to_finish SK andalso not (is_finished s)


(** REPORTER **)

datatype message = New_Items of items
                 | Goals     of term list
                 | Consider_Case of string * items
                 | Newly_Fixed of (string * typ) list (*external_name * raw type*)
                 | Internal of exn
val reporter = Thread_Data.var () : (message -> unit) Thread_Data.var
val default_reporter = K ()


fun set_reporter r = Thread_Data.put reporter (SOME r)
fun get_reporter () =
  case Thread_Data.get reporter
    of NONE => default_reporter
     | SOME r => r

fun report_goal (ctxt, SK) = (
          (case SK of HHF (st, _) :: _ =>
             (case try Logic.dest_implies (Thm.prop_of st)
                of SOME (goal, _) => get_reporter () (Goals [goal])
                 | NONE => get_reporter () (Goals []))
              | _ => raise BROKEN_INVARIANT )
          ; (ctxt, SK) )

(** Basic Operations **)

datatype counter =
    Consecutive_Counter of int
      (*Consecutive_Counter ensures sequential numbering across Minilang commands--each item's
        number is determined by its position. When a new item is inserted in the middle, it takes
        the number corresponding to that position, and all subsequent items are incremented by one*)
  | Unique_Counter of int Synchronized.var
      (*Unique_Counter ensures every item (including those that once existed) has a unique,
        immutable number. Numbers are never reassigned or changed. New items always receive the
        highest number, even when inserted in the middle.*)
  | No_Counter
      (*No_Counter disables automatic counter functionality. All bindings must be explicitly provided.
        Any attempt to auto-increment (delta > 0) will raise an error.*)

structure IPS_Data = Proof_Data (
  type T = ( counter (*counter for fixed premise*)
           * counter (*facts counter*)
           * string (*hash used for caching proof*) )
  val init = K (Consecutive_Counter 0, Consecutive_Counter 0, "")
)
val _ = Counter.make()

fun incr_premise_counter delta ctxt =
  let val (ii,jj,ID) = IPS_Data.get ctxt
   in case ii of
        Consecutive_Counter n =>
          (n, IPS_Data.put (Consecutive_Counter (n+delta), jj, ID) ctxt)
      | Unique_Counter var =>
          let val start = Synchronized.change_result var (fn i => (i, i + delta))
           in (start, IPS_Data.put (ii, jj, ID) ctxt)
          end
      | No_Counter =>
          if delta = 0 then (0, ctxt)
          else raise OPR_FAIL (INVALID_OPR, "No_Counter: all premise bindings must be explicitly provided")
  end

fun incr_fact_counter delta ctxt =
  let val (ii,jj,ID) = IPS_Data.get ctxt
   in case jj of
        Consecutive_Counter n =>
          (n, IPS_Data.put (ii, Consecutive_Counter (n+delta), ID) ctxt)
      | Unique_Counter var =>
          let val start = Synchronized.change_result var (fn i => (i, i + delta))
           in (start, IPS_Data.put (ii, jj, ID) ctxt)
          end
      | No_Counter =>
          if delta = 0 then (0, ctxt)
          else raise OPR_FAIL (INVALID_OPR, "No_Counter: all fact bindings must be explicitly provided")
  end

fun get_premise_counter ctxt =
  case #1 (IPS_Data.get ctxt) of
    Consecutive_Counter n => n
  | Unique_Counter var => Synchronized.value var
  | No_Counter => 0

fun get_fact_counter ctxt =
  case #2 (IPS_Data.get ctxt) of
    Consecutive_Counter n => n
  | Unique_Counter var => Synchronized.value var
  | No_Counter => 0

fun map_premise_counter f ctxt =
  let val (ii,jj,ID) = IPS_Data.get ctxt
   in case ii of
        Consecutive_Counter n =>
          let val (result, n') = f n
           in (result, IPS_Data.put (Consecutive_Counter n', jj, ID) ctxt)
          end
      | Unique_Counter var =>
          let val result = Synchronized.change_result var (fn n => let val (r, n') = f n in (r, n') end)
           in (result, ctxt)
          end
      | No_Counter =>
          let val (result, n') = f 0
           in if n' = 0 then (result, ctxt)
              else raise OPR_FAIL (INVALID_OPR, "No_Counter: premise counter cannot be modified")
          end
  end

fun map_fact_counter f ctxt =
  let val (ii,jj,ID) = IPS_Data.get ctxt
   in case jj of
        Consecutive_Counter n =>
          let val (result, n') = f n
           in (result, IPS_Data.put (ii, Consecutive_Counter n', ID) ctxt)
          end
      | Unique_Counter var =>
          let val result = Synchronized.change_result var (fn n => let val (r, n') = f n in (r, n') end)
           in (result, ctxt)
          end
      | No_Counter =>
          let val (result, n') = f 0
           in if n' = 0 then (result, ctxt)
              else raise OPR_FAIL (INVALID_OPR, "No_Counter: fact counter cannot be modified")
          end
  end


fun beta_eta_contract th =
  if Term.could_beta_eta_contract (Thm.prop_of th)
  then Thm.equal_elim (Drule.beta_eta_conversion (Thm.cprop_of th)) th
  else th

(* Modus Ponens *)
fun norm_tyenv tyenv
  = TVars.build (Vartab.fold (fn (N,(S,T)) => TVars.add ((N,S), Envir.norm_type tyenv T)) tyenv)

fun norm_tenv tyenv tenv =
  Vars.build (Vartab.fold (fn (N,(TY,TM)) =>
      Vars.add ((N, Envir.norm_type tyenv TY),
                    Envir.norm_term (Envir.Envir {maxidx = ~1, tenv=tenv,tyenv=tyenv}) TM
                                |> Envir.eta_contract)) tenv)

fun norm_env' (TY,TM) = (norm_tyenv TY, norm_tenv TY TM)
fun certify_tyvars ctxt = TVars.map (K (Context.cases Thm.global_ctyp_of Thm.ctyp_of ctxt))
fun certify_tmvars ctxt = Vars.map (K (Context.cases Thm.global_cterm_of Thm.cterm_of ctxt))
fun certify_vars ctxt (ty, tm) = (certify_tyvars ctxt ty, certify_tmvars ctxt tm)
fun norm_env ctxt (Envir.Envir {tenv, tyenv, ...}) = certify_vars ctxt (norm_env' (tyenv, tenv))

local fun protect_prop ctxt ctm = let open Conv
                       in case Thm.term_of ctm
                           of Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs _ =>
                                (arg_conv (abs_conv (protect_prop o snd) ctxt)) ctm
                            | Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ =>
                                (combination_conv (arg_conv (rewr_conv Thms.prop_def'sym))
                                                  (protect_prop ctxt) ctm)
                            | _ => Conv.all_conv ctm
                      end
 in
fun MP' ctxt rule thA0 =
                        let val thA = Conv.fconv_rule (protect_prop ctxt) thA0
                         in rule
                            |> Conv.fconv_rule (Conv.arg1_conv (protect_prop ctxt))
                            |> (Thm.biresolution (SOME ctxt) true [(false, thA)]
                                  THEN_ALL_NEW Thm.assumption (SOME ctxt)) 1
                            |> Seq.pull
                            |> (fn SOME (ret, _) => ret
                                 | NONE => error "BUG: CASES' MP")
                       end
end

fun MP ctxt thAB thA =
  \<^try>\<open>
  let val thAB = beta_eta_contract thAB
      val thA  = beta_eta_contract thA
      val LHS = Thm.cprop_of thAB
             |> Thm.dest_arg1

      fun qnum (\<^Const>\<open>Pure.all _\<close> $ Abs (_, _, A)) = 1 + qnum A
        | qnum _ = 0
      val diff = qnum (Thm.term_of LHS) - qnum (Thm.prop_of thA)
      val (thAB', thA') =
          if diff <= 0
          then (Thm.instantiate (Thm.match (LHS, Thm.cprop_of thA)) thAB |> beta_eta_contract,
                thA)
          else let
              val frees = Term.declare_term_frees (Thm.prop_of thA)
                              (Term.declare_term_frees (Thm.term_of LHS) Name.context)
              val names = Name.invent frees "x" diff 
              val (fixes, LHS') = fold_map (fn name => Thm.dest_abs_fresh name o Thm.dest_arg)
                                           names LHS
              val thA = Thm.incr_indexes (Thm.maxidx_of thAB + 1) thA
              val inst = Unify.smash_unifiers (Context.Proof ctxt)
                                              [(Thm.term_of LHS', Thm.prop_of thA)]
                                              (Envir.empty (Thm.maxidx_of thA + 1))
                     |> Seq.pull
                     |> (fn SOME (ret, _) => ret
                          | NONE => raise THM ("unification fail", 1, [thAB, thA]))
                     |> norm_env (Context.Proof ctxt)
              val thAB = Thm.instantiate inst thAB |> beta_eta_contract
              val xxxx = thA
              val thA  = Thm.instantiate inst thA  |> beta_eta_contract
                                                   |> fold_rev Thm.forall_intr fixes

           in (thAB, thA)
          end

   in Thm.implies_elim thAB' thA'
  end
  catch _ => MP' ctxt thAB thA \<close>


(* Helpers II *)

fun elim_conjs _ =
  let fun elim thm =
      case Thm.prop_of thm
        of \<^Const>\<open>Pure.conjunction\<close> $ _ $ _ =>
            elim (thm RS Thms.conjunctionD1) @
            elim (thm RS Thms.conjunctionD2)
         | \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>HOL.conj\<close> $ _ $ _) =>
            elim (thm RS Thms.conjunct1) @
            elim (thm RS Thms.conjunct2)
         | _ => [thm]
   in elim
  end

(* Deep destructuring of a conjunctive premise thm.

   Pushes conjunctions outward via two rewrites, then splits the resulting
   HOL.conj tree via elim_conjs:
   - all_conj_distrib: (∀x. P x ∧ Q x) ⟷ (∀x. P x) ∧ (∀x. Q x)     — always
   - imp_conjR:        (A ⟶ B ∧ C) ⟷ (A ⟶ B) ∧ (A ⟶ C)           — only if smart_size A < limit

   The rewriting is driven by a plain bottom-up conversion (Conv library,
   no Simplifier involved) so behavior is fully predictable: each matching
   position fires exactly once per pass, recursion on the result handles
   newly exposed patterns, and termination is by structural decrease on
   the total nested-conj depth. *)
local
  val all_conj_distrib_meta = @{thm HOL.all_conj_distrib} RS @{thm eq_reflection}
  val imp_conjR_meta        = @{thm HOL.imp_conjR}        RS @{thm eq_reflection}

  (* Bottom-up tree walk: descend first, try `step` at current position after
     descent, recurse on result if step fired. Atoms (Const/Free/Var/Bound)
     return reflexivity, never raise. *)
  fun walk_bu step ctxt ct =
    let
      val descent =
        case Thm.term_of ct of
          _ $ _ => Conv.combination_conv (walk_bu step ctxt) (walk_bu step ctxt) ct
        | Abs _ => Conv.abs_conv (fn (_, ctxt') => walk_bu step ctxt') ctxt ct
        | _ => Thm.reflexive ct
      val ct1 = Thm.rhs_of descent
      val step_res = Conv.try_conv step ct1
      val combined = Thm.transitive descent step_res
    in
      if Thm.is_reflexive step_res
      then combined
      else Thm.transitive combined (walk_bu step ctxt (Thm.rhs_of step_res))
    end
in
fun deep_destruct_prem ctxt thm =
  let
    val size_limit = Config.get ctxt INTRO_split_prem_conj_size_limit

    (* Single-position rewrite step. Matches only when the RHS is a HOL.conj
       (pattern-match on the term's top-of-subtree shape, cheaper than running
       rewr_conv and catching the mismatch). *)
    fun step ct =
      case Thm.term_of ct of
        Const (\<^const_name>\<open>HOL.All\<close>, _) $ Abs (_, _,
          Const (\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _) =>
            Conv.rewr_conv all_conj_distrib_meta ct
      | Const (\<^const_name>\<open>HOL.implies\<close>, _) $ ant $
          (Const (\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _) =>
            if smart_size_of_term ant < size_limit
            then Conv.rewr_conv imp_conjR_meta ct
            else Conv.no_conv ct
      | _ => Conv.no_conv ct

    (* thm's prop is Trueprop-wrapped; descend past Trueprop, then walk the
       bool-level term. *)
    val rewritten =
      Conv.fconv_rule (HOLogic.Trueprop_conv (walk_bu step ctxt)) thm
      handle CTERM _ => thm | THM _ => thm
  in elim_conjs ctxt rewritten end
end

(* Term-level preview of deep_destruct_prem: returns the bool terms
   of the atoms that deep_destruct_prem would produce. Used by AUTO_INTRO
   and compute_bindings to compute the prem → atoms mapping without
   needing an actual thm. Accepts either a bool term (to be Trueprop-wrapped)
   or an already-prop term (used directly). Detects the already-prop case
   syntactically so the check works even if the term still carries loose
   Bound indices (fastype_of would crash on those).
   When INTRO_split_prem_conj is off, behaves as an identity (returns [term])
   so callers never have to gate the call site on the config flag. *)
fun deep_destruct_term ctxt term =
  if not (Config.get ctxt INTRO_split_prem_conj) then [term]
  else
  let val prop = case term of
                   \<^Const>\<open>Trueprop\<close> $ _ => term
                 | Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ => term
                 | Const (\<^const_name>\<open>Pure.all\<close>, _) $ _ => term
                 | _ => HOLogic.mk_Trueprop term
      val cprop = Thm.cterm_of ctxt prop
      val assumed = Thm.assume cprop
      val atoms = deep_destruct_prem ctxt assumed
      fun unprop (\<^Const>\<open>Trueprop\<close> $ t) = t
        | unprop t = t
   in map (unprop o Thm.concl_of) atoms end

fun wraps ctxt ths = ths
      |> map (Conv.fconv_rule (HOLogic.Trueprop_conv (Conv.rewr_conv Thms.TAG_def'sym)))
      |> foldr1 (fn (A,B) => MP ctxt (MP ctxt Thms.conjI A) B)

val is_tagged =
  let fun chk (\<^Const>\<open>Trueprop\<close> $ X) = chk X
        | chk (\<^Const>\<open>HOL.TAG _\<close> $ _) = true
        | chk (\<^Const>\<open>HOL.conj\<close> $ A $ B) = chk A andalso chk B
        | chk (\<^Const>\<open>Pure.imp\<close> $ A $ B) = chk A orelse chk B
        | chk (\<^Const>\<open>Pure.all _\<close> $ Abs (_, _, X)) = chk X
        | chk _ = false
   in chk
  end

fun is_Trueprop (\<^Const>\<open>Trueprop\<close> $ _) = true
  | is_Trueprop _ = false

fun is_tagged_Trueprop x = is_Trueprop x andalso is_tagged x

fun remove_TAG_premises ctxt th =
  let fun conv ctxt ctm =
        let val tm = Thm.term_of ctm
         in if exists is_tagged (Logic.strip_imp_prems tm)
          then case tm
            of \<^Const>\<open>Pure.imp\<close> $ X $ _ =>
                if is_tagged_Trueprop X
                then (case X
                  of \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>conj\<close> $ _ $ _) =>
                      (Conv.rewr_conv Thms.conj_imp_eq_imp_imp
                       then_conv conv ctxt) ctm
                   | \<^Const>\<open>Trueprop\<close> $ (\<^Const>\<open>HOL.TAG _\<close> $ _) =>
                      (Conv.arg1_conv (HOLogic.Trueprop_conv (Conv.rewr_conv Thms.TAG_def))
                       then_conv conv ctxt) ctm)
                else Conv.combination_conv (Conv.arg_conv (conv ctxt)) (conv ctxt) ctm
             | \<^Const>\<open>Pure.all _\<close> $ Abs (_, _, _) =>
                  Conv.abs_conv (fn (_,ctxt) => conv ctxt) ctxt ctm
          else Conv.all_conv ctm
        end
   in if exists is_tagged (Thm.prems_of th)
      then Conv.fconv_rule (conv ctxt) th
      else th
  end

fun unwrap_conjs' ctxt th = th
      |> elim_conjs ctxt
      |> map (Conv.fconv_rule (HOLogic.Trueprop_conv (Conv.rewr_conv Thms.TAG_def)))

fun unwrap_conjs ctxt th =
      if is_Trueprop (Thm.prop_of th) andalso is_tagged (Thm.prop_of th)
      then unwrap_conjs' ctxt th
      else raise THM ("Not tagged", 0, [th])

fun unwrap_tags ctxt th =
  let val has_tag = Term.exists_Const
        (fn (\<^const_name>\<open>HOL.TAG\<close>, _) => true | _ => false)
      fun conv ctxt ctm =
        if not (has_tag (Thm.term_of ctm)) then Conv.all_conv ctm
        else case Thm.term_of ctm
           of Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs _ =>
                Conv.arg_conv (Conv.abs_conv (conv o snd) ctxt) ctm
            | Const(\<^const_name>\<open>Pure.imp\<close>, _)
                $ (Const(\<^const_name>\<open>HOL.Trueprop\<close>, _)
                    $ (Const(\<^const_name>\<open>HOL.conj\<close>, _)
                        $ (Const(\<^const_name>\<open>HOL.TAG\<close>, _) $ _)
                        $ _ ) )
                $ _ =>
              ( Conv.rewr_conv Thms.conj_imp_eq_imp_imp
              then_conv conv ctxt
              ) ctm
            | Const(\<^const_name>\<open>Pure.imp\<close>, _)
                $ (Const(\<^const_name>\<open>HOL.Trueprop\<close>, _)
                    $ (Const(\<^const_name>\<open>HOL.TAG\<close>, _) $ _) )
                $ _ =>
              ( Conv.arg1_conv (HOLogic.Trueprop_conv (Conv.rewr_conv Thms.TAG_def))
              then_conv conv ctxt
              ) ctm
            (* Bare TAG anywhere (HOL-level): unfold and continue inside.
               Subsumes the prior `Trueprop $ TAG _` premise case via the
               generic `_ $ _` recursion below. *)
            | Const(\<^const_name>\<open>HOL.TAG\<close>, _) $ _ =>
              (Conv.rewr_conv Thms.TAG_def then_conv conv ctxt) ctm
            (* Generic descent. Per-subterm `has_tag` short-circuit above
               keeps this O(size of TAG-bearing region), not O(prop). This
               is what reaches into HOL binders (∀, ⟶, ∃, …) where the IH
               from rules like nat_less_induct buries the wrapped premise. *)
            | _ $ _ => Conv.comb_conv (conv ctxt) ctm
            | Abs _ => Conv.abs_conv (fn (_, c) => conv c) ctxt ctm
            | _ => Conv.all_conv ctm
   in if has_tag (Thm.prop_of th)
    then Conv.fconv_rule (conv ctxt) th
    else th
  end

(*
fun unwrap ctxt th = th
      |> unwrap_conjs ctxt
      |> map (remove_TAG_premises ctxt)
*)

(* Maintain *)

(*
fun append_print items' (PROP (items, goal))
      = (PROP  (cat_items items' items, goal))
  | append_print items' (BUNDL (items, goal))
      = (BUNDL (cat_items items' items, goal))
*)
fun prepend_print items' (PROP (items, goal))
      = (PROP  (cat_items items items', goal))
  | prepend_print items' (BUNDL (items, goal))
      = (BUNDL (cat_items items items', goal))
  | prepend_print items' (BLOCK tree)
      = BLOCK (prepend_print items' tree)

fun maintain (c,[]) = (c,[])
  | maintain (origin as (ctxt, HHF (st, items) :: L)) =
      if no_goal' st
      then (case L
              of [] => origin
               | (HHF _ :: _) => raise BROKEN_INVARIANT
                    (* maintain (ctxt, HHF (MP ctxt st1 st, cat_items items items') :: L') *)
               | (MAGIC (cb,_,param) :: L') =>
                    (case cb ctxt (st, items, L', param) of (ctxt', S) => maintain (ctxt', S) )
               | ENDBLK _ :: _ => origin )
      else origin
  | maintain (_, MAGIC _ :: _) = raise BROKEN_INVARIANT
  | maintain (_, ENDBLK _ :: _) = raise BROKEN_INVARIANT


fun need_intro st =
  let fun need' (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _) = true
        | need' (Const(\<^const_name>\<open>Pure.all\<close>, _) $ _) = true
        | need' (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = need' X
        | need' (Const(\<^const_name>\<open>HOL.All\<close>, _) $ _) = true
        | need' (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _) = true
        | need' _ = false
   in case Thm.prop_of st
        of (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ G $ _) => need' G
         | _ => false
  end

(* Hacks *)

fun remove_typ str =
  let datatype state = MARK of state | USUAL | TYP1 | TYP of int
      fun auto _ [] = []
        | auto s (#"\127" :: L) = auto s L
        | auto (MARK s) (#"\005" :: L) = auto s L
        | auto (MARK s) (_ :: L) = auto (MARK s) L
        | auto s (#"\005" :: L) = auto (MARK s) L
        | auto USUAL (#":" :: L) = auto TYP1 L
        | auto USUAL (x :: L) = x :: auto USUAL L
        | auto TYP1 (#":" :: L) = auto (TYP 0) L
        | auto TYP1 L = #":" :: auto USUAL L
        | auto (TYP i) (#"(" :: L) = auto (TYP (i+1)) L
        | auto (TYP 0) (#")" :: L) = #")" :: auto USUAL L
        | auto (TYP i) (#")" :: L) = auto (TYP (i-1)) L
        | auto (TYP i) (_ :: L) = auto (TYP i) L
   in String.implode (auto USUAL (String.explode str))
  end

fun remove_typ_ass x = map (apsnd (map (apfst remove_typ #> apsnd (map remove_typ)))) x
fun remove_typ_ss x = map (map (apfst remove_typ #> apsnd (map remove_typ))) x

val typ_parsing_mode = Attrib.setup_config_string \<^binding>\<open>mini_typ_mode\<close> (K "flexible")

fun tolerate_typ tr fix s =
  tr s handle E as Exn.EXCEPTIONS [ERROR msg] =>
    if String.isPrefix "Undefined type name: " msg
    then let val ctxt = context_of s
      in if Config.get ctxt typ_parsing_mode = "flexible"
       then fix s
       else Exn.reraise E
     end
    else Exn.reraise E

(* Calculation *)

structure Calc_Data = Proof_Data (
  type T = (thm (*current calculation*) * int (*length of the calc chain*)) list
  val init = K []
)

fun extend_calc thm ctxt =
  if not (Config.get ctxt auto_calculation) then ([], ctxt)
  else
  let val calcs = Calc_Data.get ctxt
      val stat = Proof.init ctxt
      fun extend calc thm = stat
         |> Proof.set_facts [calc]
         |> Calculation.also NONE false
         |> Seq.pull
         |> (fn SOME (Seq.Error _, _) => NONE
              | NONE => NONE
              | SOME (Seq.Result stat, _) => stat
         |> Proof.set_facts [thm]
         |> Calculation.also NONE false
         |> Seq.pull
         |> (fn SOME (Seq.Error _, _) => NONE
              | NONE => NONE
              | SOME (Seq.Result stat, _) => stat
         |> Calculation.check
         |> (fn SOME [ret] => SOME ret
              | _ => NONE )))
      val (calcs', (_, default_calc)) =
          fold_map (fn (calc, N) => fn (M, default_calc) =>
            case extend calc thm
              of SOME calc' =>
                    if N > M
                    then ((calc', N+1), (N, SOME calc'))
                    else ((calc', N+1), (M, default_calc))
               | NONE       => ((calc, N), (M, default_calc))
          ) calcs (0, NONE)
      val calcs'N = length calcs'
      val calcs'3 =
            map_filter (fn ((i,(x, N)), (x', _)) =>
                if N > 1 andalso not (pointer_eq (x, x'))
                then SOME (calcs'N - 1 - i,x)
                else NONE
            ) (map_index I calcs' ~~ calcs)
      val calcs'' =
            if is_some default_calc
            then calcs'
            else (thm, 1) :: calcs'
      val new_facts = map (fn (i,th) =>
            (if i = 0 then "calculation" else "calculation" ^ string_of_int i, th)) calcs'3
      
   in Calc_Data.put calcs'' ctxt
   |> Proof_Context.note_thmss ""
       ( map (fn (s,th) => ((Binding.name s, []), [([th], [])]) ) new_facts )
   |> snd
   |> pair (map (apsnd (single o Thm.prop_of)) new_facts |> flatten_facts)
  end

(* transparent introduciton helpers *)

val has_prems_universal_vars =
  let fun chk (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _) = true
        | chk (Const(\<^const_name>\<open>Pure.all\<close>, _) $ _ ) = true
        | chk (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = chk X
        | chk (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _) = true
        | chk (Const(\<^const_name>\<open>HOL.All\<close>, _) $ _) = true
        | chk _ = false
   in chk
  end

fun strip_prems_universal_vars ctxt =
  let val base = get_fact_counter ctxt
      val counter = Unsynchronized.ref 0
      fun assign_name () =
        let val i = !counter
         in counter := i + 1
          ; "fact" ^ string_of_int (i + base)
        end
      fun dest (vs,hs) (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ A $ X)
            = dest (vs, (assign_name (), A) :: hs) X
        | dest (vs,hs) (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ A $ X)
            = dest (vs, (assign_name (), HOLogic.mk_Trueprop A) :: hs) X
        | dest (vs,hs) (Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (name, ty, X))
            = dest ((name,ty) :: vs, hs) X
        | dest (vs,hs) (Const(\<^const_name>\<open>HOL.All\<close>, _) $ Abs (name, ty, X))
            = dest ((name,ty) :: vs, hs) X
        | dest vh (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = dest vh X
        | dest (vs,hs) X =
            let val (vnames, ctxt) =
                      Proof_Context.add_fixes
                        (map (fn (name,typ) => (Binding.name name, SOME typ, NoSyn)) vs)
                        ctxt
                val X = subst_bounds (map Free (vnames ~~ map snd vs), X)
             in (ctxt, (rev vs, rev hs), X)
            end
   in dest ([],[])
  end

(*** COMMANDS ***)

(** INTRO **)

fun map2_opt _ [] [] = []
  | map2_opt f [] (y :: ys) = f NONE y :: map2_opt f [] ys
  | map2_opt f (x :: xs) (y :: ys) = f x y :: map2_opt f xs ys
  | map2_opt _ _ _ = raise ListPair.UnequalLengths


datatype intros_mode = ALL_SUBGOALS | SINGLE_GOAL

fun strip_meta_hhf term =
  let fun strip (V,P) (Const("Pure.imp", _) $ H $ B) = strip (V,H::P) B
        | strip (V,P) (Const("Pure.all", _) $ Abs (a, T, B)) = strip ((a,T)::V,P) B
        | strip (V,P) (\<^Const>\<open>Pure.all ty\<close> $ X) =
            strip (V,P) (\<^Const>\<open>Pure.all ty\<close> $ Abs ("_", ty, Term.incr_boundvars 1 X $ Bound 0))
        | strip (V,P) X = (rev V, rev P, X)
   in strip ([],[]) term end

val strip_meta_and_hol_hhf = Minilang_Aux.strip_meta_and_hol_hhf

fun quantifier_bindings ctxt st =
         Thm.prop_of st
      |> Logic.dest_implies |> fst
      |> strip_meta_hhf
      |> #1
      |> (fn L => fold_map (fn (name, ty) => fn ctxt =>
                      variant_name name ctxt |> apfst (rpair ty)
                  ) L (Variable.names_of ctxt))
      |> #1

val conjI = @{thm conjI}
val asm_rl = @{thm asm_rl}
fun split_conjs sequent =
  let fun chk_conj_num ret (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = chk_conj_num ret X
        | chk_conj_num ret (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ B) = chk_conj_num (ret + 1) B
        | chk_conj_num ret (Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _, X)) = chk_conj_num ret X
        | chk_conj_num ret (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = chk_conj_num ret X
        | chk_conj_num ret _ = ret
      val num = chk_conj_num 1 (Thm.major_prem_of sequent)
      fun mk_rule num =
        if num <= 2 then @{thm conjI} else mk_rule (num - 1) RSN (2, @{thm conjI})
   in if num <= 1
   then sequent
   else mk_rule num RS sequent
  end

fun is_conj_goal st =
  let fun chk (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = chk X
        | chk (Const(\<^const_name>\<open>HOL.conj\<close>, _) $ _ $ _) = true
        | chk (Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _, X)) = chk X
        | chk (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = chk X
        | chk _ = false
   in case Thm.prop_of st
        of (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ G $ _) => chk G
         | _ => false
  end

fun SPLIT_CONJS' (ctxt, HHF (st, items) :: L) =
    if is_conj_goal st
    then (ctxt, HHF (protect_goals (split_conjs st), items) :: L)
    else raise OPR_FAIL (INVALID_OPR, "SPLIT_CONJS: the leading goal is not a conjunction")
  | SPLIT_CONJS' _ = raise BROKEN_INVARIANT

(* INTRO'' performs introduction rules (allI and impI) on the current goal.
   Parameters:
   - F: Processing function that handles the focused subgoal.
        Takes binds (string list) and (st, foc) where binds are the actual variable names used,
        st is the theorem state and foc contains focus information,
        returns (st'', (items', ctxt')) with the updated state, new proof items, and context.
   - mode: Introduction mode controlling how subgoals are processed:
        * ALL_SUBGOALS: recursively apply INTRO'' to all resulting subgoals
        * SINGLE_GOAL: only process the current goal
   - bs: Optional list of variable bindings (string list option).
        If SOME bindings, uses the provided names for introduced quantified variables.
        If NONE, uses default variable names from the goal.
*)
fun INTRO'' F mode bs (origin as (ctxt, HHF (st0, items) :: L)) =
    if Thm.no_prems st0 then (empty_items, origin)
    else if need_intro st0
      then let val st = st0
                     |> Seq.REPEAT (Thm.biresolution NONE true
                              [(false, Thms.allI), (false, Thms.impI)] 1)
                     |> Seq.hd

               val default_binds = quantifier_bindings ctxt st |> map fst
               val binds = case bs
                             of NONE => default_binds
                              | SOME bs'0 =>
                                  let val bs' = if member (op =) ["COMPLETE_NEXT", "RELAXED"]
                                                                 (Config.get ctxt working_mode)
                                                then take (length default_binds) bs'0
                                                else bs'0
                                   in map2_opt (fn NONE => I
                                                 | SOME b => K b) bs' default_binds
                                      handle ListPair.UnequalLengths =>
                                        raise OPR_FAIL (INVALID_OPR, "Incorrect number of VARS")
                                  end
               val (foc, st') = Subgoal.focus_prems ctxt 1 (SOME (map Binding.name binds)) st
               val (st''m, (items', ctxt')) = F binds (st', foc)
               val _ = get_reporter () (New_Items items')
               val mode_mk_block = Config.get ctxt INTRO_mk_block
               val st'' = st''m
               fun PRT _ t0 =
                    let val t = if mode_mk_block then BLOCK t0 else t0
                     in case print_stack [(HHF (st0, items))]
                     of BUNDL (items, goals) =>
                          BUNDL (items, t :: tl goals)
                      | PROP  (items, _) =>
                          prepend_print items t
                      | _ => raise BROKEN_INVARIANT
                    end
               fun CB ctxt'' (st'',_,S, CASE_NAME bs) =
                let val st'3 = singleton (Proof_Context.export ctxt'' ctxt') st''
                 in (ctxt, HHF (
                           Subgoal.retrofit ctxt'' ctxt (#params foc) (#asms foc) 1 st'3 st
                        |> Seq.hd
                        |> conclude_goal,
                      ([],[])) :: S)
                 |> mode = ALL_SUBGOALS ? (#2 o INTRO'' F mode bs)
                end
                 | CB _ _ = raise BROKEN_INVARIANT
               val result_state = if num_goals_of' st0 > 1
                                  then (ctxt', HHF (st'', items') :: ENDBLK T_NXT :: MAGIC (CB,PRT,CASE_NAME NONE) :: L)
                                  else (ctxt', HHF (st'', items') :: MAGIC (CB,PRT,CASE_NAME NONE) :: L)
            in (items', result_state)
           end
      else (empty_items, origin)
  | INTRO'' _ _ _ _ = raise BROKEN_INVARIANT

fun INTRO' mode split_prem_conj_opt bs premise_names s =
  let val _ = if mode = ALL_SUBGOALS andalso is_some premise_names
              then raise OPR_FAIL (INVALID_OPR, "premise_names must be NONE in ALL_SUBGOALS mode")
              else ()
      fun F binds (st, foc) =
        let val num_prems = length (#prems foc)
            val _ = case premise_names
                      of SOME names =>
                          if length names <> num_prems
                          then raise OPR_FAIL (INVALID_OPR, "bad premise binding number")
                          else ()
                       | NONE => ()
            val do_split_prem_conj =
                  case split_prem_conj_opt
                    of SOME b => b
                     | NONE => Config.get (#context foc) INTRO_split_prem_conj
            val (bindings, ctxt) = map_premise_counter (fn counter_val =>
                  fold_map (fn (d, th) => fn current_counter =>
                    let val (name, next_counter) =
                          case premise_names of
                            SOME names =>
                              (case nth names d of
                                 SOME n => (n, current_counter)  (* Use provided name, including "" for skip *)
                               | NONE => (assm_name current_counter, current_counter + 1))
                          | NONE => (assm_name current_counter, current_counter + 1)
                        val thms = if do_split_prem_conj andalso name <> ""
                                   then deep_destruct_prem (#context foc) th
                                   else [th]
                     in (((Binding.name name, []), [(thms, [])]), next_counter)
                    end
                  ) (map_index I (#prems foc)) counter_val
                ) (#context foc)
            (* Filter out bindings with empty names, then group same-named
               entries so that e.g. two premises both named "h" become a
               single note_thmss entry with two thms — yielding h(1), h(2)
               via flatten_facts instead of shadowing. *)
            val bindings_filtered = filter (fn ((b, _), _) => Binding.name_of b <> "") bindings
            val bindings_grouped =
              fold_rev (fn entry as ((b, attrs), thms_attrs) => fn acc =>
                let val name = Binding.name_of b
                in case acc of
                     ((b', attrs'), thms_attrs') :: rest =>
                       if name = Binding.name_of b'
                       then ((b', attrs'), thms_attrs @ thms_attrs') :: rest
                       else entry :: acc
                   | [] => [entry]
                end
              ) bindings_filtered []
         in ctxt
         |> Proof_Context.note_thmss "" bindings_grouped
         |> apfst (map (apsnd (map Thm.prop_of))
                #> flatten_facts
                #> pair (map2 (fn bind => fn (_, cterm) => (bind, Thm.typ_of_cterm cterm)) binds (#params foc)))
         |> pair st
        end
   in INTRO'' F mode bs s
  end

fun TRANSPARENT_INTRO' (origin as (ctxt, HHF (st, _) :: _)) =
      if Config.get ctxt transparent_intro andalso
         has_prems_universal_vars (fst (Logic.dest_implies (Thm.prop_of st)))
      then #2 (INTRO' SINGLE_GOAL NONE NONE NONE origin)
      else origin
  | TRANSPARENT_INTRO' _ = raise BROKEN_INVARIANT


fun raw_apply msg report tac timeout (ctxt, HHF (st, facts) :: L) =
    ( case (case timeout
              of SOME time => Timeout.apply time (Seq.pull o tac) (ctxt, st)
               | NONE      => Seq.pull (tac (ctxt, st)) )
        of NONE => raise OPR_FAIL (PROOF_FAIL, msg)
         | SOME (Seq.Result (ctxt', st'), _) =>
            (* Emit only the NEW subgoals introduced by this tactic
               application (which always targets subgoal 1), not the full
               prems list. If the pre-state `st` had K prems and the rule
               adds M prems in place of subgoal 1, st' has K-1+M prems
               with the M new ones at positions 1..M. Dropping the K-1
               siblings is crucial for correct child-count reporting when
               the tactic runs inside an outer subgoal context (e.g.
               nested InferenceRule). *)
            let val n_new = Thm.nprems_of st' - Thm.nprems_of st + 1
                val new_goals = take n_new (Thm.prems_of st')
             in report (Goals new_goals)
              ; (ctxt', HHF (protect_goals st', facts) :: L)
            end
         | SOME (Seq.Error E, _) => raise OPR_FAIL (PROOF_FAIL, E ()) )
  | raw_apply _ _ _ _ _ = raise BROKEN_INVARIANT

fun apply' msg report tac timeout s = maintain (raw_apply msg report tac timeout s)

fun apply msg tac time s = apply' msg (get_reporter()) tac time s
      handle Timeout.TIMEOUT _ => raise OPR_FAIL (PROOF_FAIL, "Timeout")

fun apply_method msg using meth timeout s = apply msg (meth using) timeout s


fun record_history name (s,his,ID) = (s, Symtab.update (name,s) his,ID)
fun restore_history name (_,his,ID) =
    case Symtab.lookup his name
      of NONE => raise OPR_FAIL (INVALID_OPR, "history " ^ name ^ " not found")
       | SOME s => (s, his,ID)

fun SKIP_SUCCESS F (SK as (_, HHF (st,_) :: _)) =
        if Thm.no_prems st then SK else F SK
  | SKIP_SUCCESS F SK = F SK

fun OPR_NO_INCR (f : stack -> stack) ((S,TAB,ID) : state) : state
  = (f S, TAB, ID)
fun OPR (f : stack -> stack) ((S,TAB,ID) : state) : state
  = (f S, TAB, ID+1)
fun OPR_ID (f : int -> stack -> stack) ((S,TAB,ID) : state) : state
  = (f ID S, TAB, ID+1)

(* OPR_with_ret: for operations that return ('a, stack) *)
fun OPR_with_ret (f : stack -> 'a * stack) ((S,TAB,ID) : state) : 'a * state
  = let val (ret, S') = f S
     in (ret, (S', TAB, ID+1))
    end

fun timed_OPR t f s
  = Timeout.apply (Time.fromSeconds t) (OPR f) s
    handle Timeout.TIMEOUT _ => raise OPR_FAIL (PROOF_FAIL, "Timeout")
         | Exn.Interrupt_Breakdown => raise OPR_FAIL (PROOF_FAIL, "Timeout")

fun timed_OPR_with_ret t f s
  = Timeout.apply (Time.fromSeconds t) (OPR_with_ret f) s
    handle Timeout.TIMEOUT _ => raise OPR_FAIL (PROOF_FAIL, "Timeout")
         | Exn.Interrupt_Breakdown => raise OPR_FAIL (PROOF_FAIL, "Timeout")

val SPLIT_CONJS = timed_OPR 5 SPLIT_CONJS'
val SPLIT_CONJS_CMD = Scan.succeed (timed_OPR 5 SPLIT_CONJS')

fun CONTEXTUAL_CMD (parser : Proof.context -> command)
                   (toks : Token.src)
  = ((fn (s:state) => fst (parser (#1 (#1 s)) toks) s), [])


val VARS_KWD  = (Parse.$$$ "VARS" || Parse.$$$ "vars")
val PREMS_KWD = (Parse.$$$ "PREMISES" || Parse.$$$ "premises")
val OPT_VARS  = Scan.option (VARS_KWD  |-- Parse.and_list (Scan.repeat1 (Parse.maybe Parse.name)) >> flat)
val OPT_PREMS = Scan.option (PREMS_KWD |-- Parse.and_list (Scan.repeat1 (Parse.maybe Parse.name)) >> flat)
val VARS = VARS_KWD |-- Parse.and_list (Scan.repeat1 Parse.binding) >> flat
val IN = (Parse.$$$ "IN" || Parse.$$$ "in")




(*fun INTRO_ALL (ctxt, HHF (st, facts) :: L) = *)


(** APPLY **)

val mini_single_cmd_timeout = Attrib.setup_config_int \<^binding>\<open>mini_single_cmd_timeout\<close> (K 15000)

fun gen_APPLY prep_thms timeout using text =
      OPR (fn SK as (ctxt, _) =>
        apply_method "Fail to apply the tactic"
                     (prep_thms ctxt using) (Method.evaluate text ctxt) timeout SK)
val APPLY   = gen_APPLY (K I)
val APPLY'' = gen_APPLY Attrib.eval_thms

val APPLY_CMD = (Method.parse -- Scan.optional WITH_CLAUSE [])
             >> (fn ((m,_),using) => fn s =>
                let val timeout = Config.get (context_of s) mini_single_cmd_timeout
                               |> Time.fromMilliseconds
                 in APPLY'' (SOME timeout) using m s
                end )

(** UNFOLD **)

(** definition retrieval **)

(* Retrieve all potential definitions of a constant by trying multiple naming suffixes
   and searching for definitional equations with all possible arities *)
fun potential_defs_of_const ctxt const_name =
  let
    val thy = Proof_Context.theory_of ctxt
    val base_name = Long_Name.base_name const_name
    val const_type_opt = try (Sign.the_const_type thy) const_name

    (* Standard definition suffixes to try *)
    val suffixes = ["_def", "_def2", "_alt", "_alt_def", "_altdef",
                    "_del_alt", "_alt_def2", ".simps"]

    (* Normalize theorem by eliminating universal quantifiers and implications *)
    fun normalize_thm thm =
      let
        fun strip_concl (@{const Trueprop} $ t) = t
          | strip_concl t = t
        val concl = strip_concl (Thm.concl_of thm)
      in
        case concl of
          Const (@{const_name HOL.All}, _) $ _ =>
            normalize_thm (thm RS @{thm spec})
        | Const (@{const_name HOL.implies}, _) $ _ $ _ =>
            normalize_thm (thm RS @{thm mp})
        | _ => thm
      end
      handle THM _ => thm

    fun check_head h = case h of Const (c, _) => c = const_name
                                 | Free (c, _) => c = const_name
                                 | _ => false

    fun is_definitional_eq thm =
      let
        fun check_lhs (Const (@{const_name HOL.eq}, _) $ lhs $ _) =
              check_head (Term.head_of lhs)
          | check_lhs (Const (@{const_name Pure.eq}, _) $ lhs $ _) =
              check_head (Term.head_of lhs)
          | check_lhs (@{const Trueprop} $ t) = check_lhs t
          | check_lhs (Const (@{const_name Pure.all}, _) $ Abs (_, _, body)) = check_lhs body
          | check_lhs (Const (@{const_name HOL.All}, _) $ Abs (_, _, body)) = check_lhs body
          | check_lhs (Const (@{const_name Pure.imp}, _) $ _ $ consequent) = check_lhs consequent
          | check_lhs (Const (@{const_name HOL.implies}, _) $ _ $ consequent) = check_lhs consequent
          | check_lhs _ = false
      in
        check_lhs (Thm.concl_of thm)
      end

    fun try_suffix suffix =
      let
        val name = base_name ^ suffix
        val facts = Proof_Context.facts_of ctxt
        val internal_name = Facts.intern facts name
        val thms = (try (Proof_Context.get_thms ctxt) name) |> the_default []
      in
        map (fn thm => (internal_name, thm)) thms
      end

    val named_defs = maps try_suffix suffixes

    (* Search with Find_Theorems for all arities *)
    val search_results =
      case const_type_opt of
        SOME const_type =>
          let
            val (arg_types, result_type) = Term.strip_type const_type
            val max_arity = length arg_types

            (* Construct term pattern for n arguments *)
            fun make_pattern n_args =
              let
                val used_arg_types = take n_args arg_types
                val arg_vars = map_index
                  (fn (i, arg_ty) => Var (("x", i), arg_ty))
                  used_arg_types
                val const_term = Const (const_name, const_type)
                val lhs = Term.list_comb (const_term, arg_vars)

                val remaining_types = drop n_args arg_types
                val rhs_type =
                  if null remaining_types then result_type
                  else remaining_types ---> result_type

                val rhs = Var (("rhs", 0), rhs_type)
              in
                HOLogic.mk_eq (lhs, rhs)
              end

            (* Search for each arity 0 to max_arity *)
            fun search_with_arity n =
              let
                val pattern = make_pattern n
                val criterion = [(true, Find_Theorems.Pattern pattern)]
                val (_, results) =
                  Find_Theorems.find_theorems ctxt NONE NONE true criterion
              in
                map (fn (fact_ref, thm) => (Facts.string_of_ref fact_ref, thm)) results
              end
              handle ERROR _ => []
          in
            maps search_with_arity (0 upto max_arity)
          end
      | NONE => []

    val all_defs = filter (fn (_, thm) => is_definitional_eq thm) (named_defs @ search_results)
    val normalized_defs = map (fn (name, thm) => (name, normalize_thm thm)) all_defs
  in
    distinct (Thm.eq_thm_prop o apply2 snd) normalized_defs
  end

fun UNFOLD' prep_thms raw_defs (ctxt, HHF (st, items) :: S) =
  let val defs = prep_thms ctxt raw_defs
      val st' = Local_Defs.unfold_goals ctxt defs st
   in (ctxt, HHF (st', items) :: S)
   |> report_goal
  end
  | UNFOLD' _ _ _ = raise BROKEN_INVARIANT

fun UNFOLD_FACT' prep_thms raw_defs fact_names (ctxt, SK as HHF (st, items) :: S) =
  let val defs = prep_thms ctxt raw_defs
      val fact_names = if member (op =) fact_names "*"
                       then context_of_leading_goal (print_stack SK)
                         |> #1 |> #2
                         |> map (#1 #> simp_fact_name')
                       else fact_names
      val facts = map ( Proof_Context.get_thms ctxt
                     #> map ( Local_Defs.unfold ctxt defs ) ) fact_names
   in ctxt
   |> Proof_Context.note_thmss "" ( map (rpair [] o Binding.name) fact_names
                                      ~~ map (single o rpair []) facts)
   |-> (fn new_facts =>
     rpair (HHF (st, cat_items ([], map (apsnd (map Thm.prop_of)) new_facts |> flatten_facts) items) :: S))
  end
  | UNFOLD_FACT' _ _ _ _ = raise BROKEN_INVARIANT

val UNFOLD = timed_OPR 2 o UNFOLD' (K I)
val UNFOLD_CMD = Parse.thms1 -- Scan.option (IN |-- Scan.repeat1 Parse.name) >> (
      fn (defs, NONE)       => timed_OPR 2 (UNFOLD' Attrib.eval_thms defs)
       | (defs, SOME facts) => timed_OPR 4 (UNFOLD_FACT' Attrib.eval_thms defs facts) )


(** INITIATION PROCESS **)

(* Flexible Type *)

(*either ["", "no_typ", "flexible"]*)

fun typ_parsing ctxt terms =
  let fun filter_out_typ (Const ("_type_constraint_", _) $ X) = X
        | filter_out_typ (origin as (A $ B)) =
            let val A' = filter_out_typ A
                val B' = filter_out_typ B
             in if pointer_eq (A, A') andalso pointer_eq (B, B')
              then origin
              else A' $ B'
            end
        | filter_out_typ (origin as (Abs (N,T,X))) =
            let val X' = filter_out_typ X
             in if pointer_eq (X, X')
              then origin
              else Abs (N,T,X')
            end
        | filter_out_typ X = X
   in case Config.get ctxt typ_parsing_mode
   of "" => terms
    | "no_typ" => map filter_out_typ terms
    | "flexible" =>
        let val ctxt't = Config.put typ_parsing_mode "" ctxt
         in if can (Syntax.check_terms ctxt't) terms
           then terms
           else map filter_out_typ terms
        end
    | wrong => error ("Minilang.mini_typ_mode must be either [\"\", \"no_typ\", \"flexible\"] but " ^
                      wrong ^ " is given.")
  end

(*...*)

fun NEED_STANDARD (ctxt, HHF (st, _) :: _) = Phi_Sledgehammer_Solver.need_standard_tac ctxt st
  | NEED_STANDARD _ = false

fun TRY_STANDARD SK =
  if NEED_STANDARD SK
  then apply' "Fail to apply the tactic"
              (K ()) (CONTEXT_TACTIC (Classical.standard_tac (#1 SK) [])) NONE SK
  else SK

fun INTRO mode spco bs pn = timed_OPR_with_ret 5000 (INTRO' mode spco bs pn)
val INTRO_CMD = (OPT_VARS -- OPT_PREMS)
        >> (fn args => fn s => #2 (timed_OPR_with_ret 2 (uncurry (INTRO' SINGLE_GOAL NONE) args) s))
val INTRO_ALL_CMD = (OPT_VARS -- OPT_PREMS)
        >> (fn args => fn s => #2 (timed_OPR_with_ret 2 (uncurry (INTRO' ALL_SUBGOALS NONE) args) s))
val TRANSPARENT_INTRO = OPR_NO_INCR TRANSPARENT_INTRO'

local
(*
fun read_trrules thy raw_rules =
  let
    val ctxt = Proof_Context.init_global thy;
    val read_root =
      #1 o dest_Type o Proof_Context.read_type_name {proper = true, strict = false} ctxt;
  in
    raw_rules
    |> map (Syntax.map_trrule (fn (r, s) => Syntax_Phases.parse_ast_pattern ctxt (read_root r, s)))
  end;

val trrules = read_trrules \<^theory> [
      Syntax.Parse_Rule (("logic", "(a \<le> b) \<le> c"), ("logic", "a \<le> b \<and> b \<le> c")),
      Syntax.Parse_Rule (("logic", "(a < b) < c"), ("logic", "a < b \<and> b < c")),
      Syntax.Parse_Rule (("logic", "a = b = c"), ("logic", "a = b \<and> b = c")),
      Syntax.Parse_Rule (("logic", "a \<longleftrightarrow> b \<longleftrightarrow> c"), ("logic", "a \<longleftrightarrow> b \<and> b \<longleftrightarrow> c"))
  ]
*)

val term_qchk = exists_subterm (
      fn Const(\<^const_name>\<open>less\<close>, _) $ (Const(\<^const_name>\<open>less\<close>, _) $ _ $ _) $ _ => true
       | Const(\<^const_name>\<open>less_eq\<close>, _) $ (Const(\<^const_name>\<open>less_eq\<close>, _) $ _ $ _) $ _ => true
       | Const("HOL.eq", _) $ (Const("HOL.eq", _) $ _ $ _) $ _ => true
       | Const("HOL.iff", _) $ _ $ (Const("HOL.iff", _) $ _ $ _) => true
       | _ => false )


fun term_check tm =
  if term_qchk tm
  then let
      fun maptm (Const(\<^const_name>\<open>less\<close>, _) $ (Const(\<^const_name>\<open>less\<close>, T1) $ A $ B) $ C)
            = \<^Const>\<open>conj\<close> $ (Const(\<^const_name>\<open>less\<close>, T1) $ A $ B)
                          $ (Const(\<^const_name>\<open>less\<close>, T1) $ B $ C)
        | maptm (Const(\<^const_name>\<open>less_eq\<close>, _) $ (Const(\<^const_name>\<open>less_eq\<close>, T1) $ A $ B) $ C)
            = \<^Const>\<open>conj\<close> $ (Const(\<^const_name>\<open>less_eq\<close>, T1) $ A $ B)
                          $ (Const(\<^const_name>\<open>less_eq\<close>, T1) $ B $ C)
        | maptm (Const("HOL.eq", _) $ (Const("HOL.eq", T1) $ A $ B) $ C)
            = \<^Const>\<open>conj\<close> $ (Const("HOL.eq", T1) $ A $ B)
                          $ (Const("HOL.eq", T1) $ B $ C)
        | maptm (Const("HOL.iff", _) $ (Const("HOL.iff", T1) $ A $ B) $ C)
            = \<^Const>\<open>conj\<close> $ (Const("HOL.iff", T1) $ A $ B)
                          $ (Const("HOL.iff", T1) $ B $ C)
        | maptm (origin as (A $ B)) =
            let val A' = maptm A
                val B' = maptm B
             in if pointer_eq (A', A) andalso pointer_eq (B', B)
                then origin
                else A' $ B'
            end
        | maptm (origin as Abs (N,T,X)) =
            let val X' = maptm X
             in if pointer_eq (X', X)
                then origin
                else Abs (N, T, X')
            end
        | maptm X = X
   in maptm tm
  end
  else tm

in

fun INIT_SYNTAX ctxt = ctxt
  |> Proof_Context.notation false Syntax.mode_default [
      (Const (\<^const_name>\<open>less_eq\<close>, dummyT), Mixfix (Input.string "(_/ \<le> _)", [51, 51], 50, Position.no_range)),
      (Const (\<^const_name>\<open>less\<close>,    dummyT), Mixfix (Input.string "(_/ < _)",     [51, 51], 50, Position.no_range))
    ]
  |> Proof_Context.notation true Syntax.mode_default [
      (Const (\<^const_name>\<open>less_eq\<close>, dummyT), Mixfix (Input.string "(_/ \<le> _)", [50, 51], 50, Position.no_range)),
      (Const (\<^const_name>\<open>less\<close>,    dummyT), Mixfix (Input.string "(_/ < _)",     [50, 51], 50, Position.no_range))
    ]
  |> Context.proof_map (
        Syntax_Phases.term_check ~200  "a < b < c" (K (map term_check)))

end


(* INIT *)

fun init_ctxt c st = c
  |> IPS_Data.put (
        let val mode = Config.get c counter_mode
            val (premise_ctr, fact_ctr) =
              case mode of
                "consecutive" => (Consecutive_Counter 0, Consecutive_Counter 0)
              | "unique" => (Unique_Counter (Synchronized.var "premise_counter" 0),
                             Unique_Counter (Synchronized.var "fact_counter" 0))
              | "none" => (No_Counter, No_Counter)
              | _ => error ("Invalid counter_mode: " ^ mode ^ ". Must be one of: consecutive, unique, none")
         in (premise_ctr, fact_ctr, Hasher.term (Thm.prop_of st))
        end
      )
  |> Context.proof_map (
        Syntax_Phases.term_check ~10000 "minlang-flexible-typ" typ_parsing
    )

val install_relaxed_typ_parsing = Syntax_Phases.term_check ~10000 "minlang-flexible-typ" typ_parsing

fun INIT c st =
  let val st0 = if Config.get c auto_deconflict_bound
                then deconflict_bound_names_thm st
                else st
      val facts = Proof_Context.facts_of c
      val facts' = if can Local_Theory.assert c
                   then Proof_Context.facts_of (Local_Theory.target_of c)
                   else Global_Theory.facts_of (Proof_Context.theory_of c)
      val local_facts =
        Facts.dest_static false [facts'] facts
          |> map (apsnd (map Thm.prop_of))
          |> flatten_facts
          |> filter_redundant_facts

      val (vars, _) = Variable.constraints_of c
      val vars' = Vartab.fold (fn ((N,~1),T) => (fn L => (N,T) :: L)
                                | _ => I) vars []
      val st' = init_goal c st0
   in ((init_ctxt c st0, [HHF (st', (vars',local_facts)), ENDBLK T_END]), Symtab.empty, 0)
  end

fun INIT'  st = INIT (Proof.context_of st) (#goal (Proof.simple_goal st))

(** Crush **)

val crush_timeout = Attrib.setup_config_int \<^binding>\<open>crush_timeout\<close> (K 8) (*in seconds*)

fun SIMP' _ _ (ctxt, []) = (ctxt, [])
  | SIMP' prep_with raw_with_lems SK0 =
    TRY_STANDARD SK0 |> (fn (s as (ctxt, _)) =>
  let val with_lems = prep_with ctxt raw_with_lems
      val ctxt = apply_WITH with_lems ctxt
      val s = (case s of (c, HHF (st, facts) :: L) =>
                  (c, HHF (Pre_Simproc.pre_simproc_on_sequent ctxt st, facts) :: L)
                | _ => s)
      val time = Config.get ctxt crush_timeout
              |> Time.fromSeconds
      val reporter = get_reporter ()
      val msg = "Cannot further simplify the goal. You should either apply other operation or \
                \supply more simplification rules."
   in
   (( raw_apply msg reporter
                (CONTEXT_TACTIC (CHANGED (Clasimp.auto_tac ctxt))) (SOME time) s
      handle Timeout.TIMEOUT _ => 
      raw_apply msg reporter
                (CONTEXT_TACTIC (CHANGED (Clasimp.clarsimp_tac (Smart_Split.add_smart_split ctxt) 1))) (SOME time) s)
      handle OPR_FAIL E =>
                (case s of (_, HHF (st, _) :: _) =>
                                if (*need_intro st orelse*) NEED_STANDARD SK0
                                then s
                                else raise OPR_FAIL E
                         | _ => raise OPR_FAIL E )
           | Timeout.TIMEOUT _ =>
                raise OPR_FAIL (PROOF_FAIL, "Timeout"))
  end)

fun CRUSH' prep_with (vars, raw_with_lems) SK0 =
     SIMP' prep_with raw_with_lems SK0
  |> SKIP_SUCCESS (#2 o INTRO' ALL_SUBGOALS NONE vars NONE)
  |> report_goal


val SIMP   = OPR o (report_goal oo SIMP'  (K I))
val SIMP'' = OPR o (report_goal oo SIMP'  read_with)
val CRUSH  = OPR o (CRUSH' (K I))

val SIMP_CMD  = with_parser >> SIMP''
val CRUSH_CMD = ( OPT_VARS -- with_parser )
             >> (OPR o CRUSH' read_with)

(** SIMPLIFY_GOAL_AND_PREMISES' **)

(* Helper conversions for wrapping/unwrapping NO_SIMP protection on goal conclusions.

   NO_SIMP is wrapped at the META level (around Trueprop XXX) rather than at
   the object level (inside Trueprop). This makes NO_SIMP invisible to the
   classical reasoner, which operates on object-level propositions inside
   Trueprop. Previously, wrapping inside Trueprop exposed NO_SIMP(False) to
   the classical reasoner, which could leak '¬ NO_SIMP False' into new
   premises via classical interactions. *)
local
  open Conv
  val NO_SIMP_def_sym = @{thm NO_SIMP_def[symmetric]}
  val NO_SIMP_def = @{thm NO_SIMP_def}

  (* Traverse the meta-level structure (⋀x. ... ⟹ ... ⟹ conclusion) to reach
     the conclusion and apply the transform there. Stops at Trueprop so the
     transform wraps the entire Trueprop(...) at the meta level. *)
  fun traverse_to_conclusion transform ctxt' ctm =
    case Thm.term_of ctm of
      Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs _ =>
        arg_conv (abs_conv (traverse_to_conclusion transform o snd) ctxt') ctm
    | Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ =>
        arg_conv (traverse_to_conclusion transform ctxt') ctm
    | _ => transform ctm

in
  (* Wrap goal conclusion (at the prop level, around Trueprop) with NO_SIMP *)
  fun wrap_goal_conclusion_NO_SIMP ctxt =
    traverse_to_conclusion (rewr_conv NO_SIMP_def_sym) ctxt

  (* Unwrap NO_SIMP from the meta-level goal conclusion after simplification *)
  fun unwrap_goal_conclusion_NO_SIMP ctxt =
    let fun unwrap ctm =
          case Thm.term_of ctm of
            Const(\<^const_name>\<open>NO_SIMP\<close>, _) $ _ =>
              (rewr_conv NO_SIMP_def then_conv unwrap) ctm
          | _ => all_conv ctm
    in traverse_to_conclusion unwrap ctxt end
end

(* Main operation function *)
fun SIMPLIFY_GOAL_AND_PREMISES'
    (simp_facts: thm list)
    (extra_simprocs: simproc list)
    (use_system_simps: bool)
    (premise_names: string list)
    (simplify_goal: bool)
    (naming_fn_opt: (term list -> string list) option)
    (naming_vars_fn_opt: ((string * typ) list -> string list) option)
    (timeout: Time.time option)
    (origin as (ctxt, HHF (st0, items) :: S)) =
  let
    (* 1. Retrieve premises by name from context *)
    val prem_thms =
      flat (map (fn name =>
        Proof_Context.get_thms ctxt name
        handle ERROR msg =>
          raise OPR_FAIL (INVALID_OPR, "Premise fact '" ^ name ^ "' not found: " ^ msg))
      premise_names)

    (* Store original premise terms for comparison *)
    val orig_prem_terms = map Thm.prop_of prem_thms
    val orig_goal_prems = Logic.strip_imp_prems (Thm.prop_of st0)

    (* 2. Insert premises into the goal *)
    val st_with_prems =
      case SINGLE (Method.insert_tac ctxt prem_thms 1) st0 of
        SOME st' => st'
      | NONE => raise OPR_FAIL (PROOF_FAIL, "Failed to insert premises into goal")

    (* 3. Protect goal conclusion with NO_SIMP if not simplifying it *)
    val st_protected =
      if simplify_goal then st_with_prems
      else Conv.gconv_rule (wrap_goal_conclusion_NO_SIMP ctxt) 1 st_with_prems

    (* 3.5. Pre-simproc preprocessing *)
    val st_protected = Pre_Simproc.pre_simproc_on_sequent ctxt st_protected

    (* 4. Setup simplifier context *)
    val simp_ctxt = (
      if use_system_simps
      then ctxt addsimps simp_facts
      else Simplifier.clear_simpset ctxt addsimps simp_facts
      ) |> (fn c => c addsimprocs extra_simprocs)
        |> Simplifier.add_cong @{thm NO_SIMP_cong}

    (* 5. Apply simplification using conversion *)
    fun do_clarsimp () =
      (CHANGED_PROP (Clasimp.clarsimp_tac (Smart_Split.add_smart_split simp_ctxt) 1) st_protected |> Seq.hd
       handle Option.Option =>
         raise OPR_FAIL (PROOF_FAIL,
           "The simplification made no progress."))
      |> Config.get ctxt auto_deconflict_bound ? deconflict_bound_names_thm
    val st_simplified =
      case timeout of SOME t => Timeout.apply t do_clarsimp ()
                    | NONE => do_clarsimp ()
  in
    (* If clarsimp completely solved the goal (e.g. a contradictory premise),
       skip the wrap/INTRO/unwrap steps — mirrors the SKIP_SUCCESS pattern in CRUSH' *)
    if Thm.no_prems st_simplified
    then (empty_items, (ctxt, HHF (st_simplified, items) :: S))
    else let

    (* 6. Protect goal conclusion to prevent INTRO's allI/impI from affecting it *)
    val st_protected_for_intro =
      Conv.gconv_rule (wrap_goal_conclusion_NO_SIMP ctxt) 1 st_simplified

    (* 7. Extract premises from the first subgoal *)
    val (_, prems_after_intro, _) = strip_meta_hhf (fst (Logic.dest_implies (Thm.prop_of st_protected_for_intro)))

    (* 8. Helper: check if a premise is unchanged *)
    fun is_unchanged prem_term =
      exists (fn orig => Term.aconv (orig, prem_term)) orig_prem_terms
      orelse exists (fn orig => Term.aconv (orig, prem_term)) orig_goal_prems

    (* 9. Generate premise names: SOME "" for unchanged, SOME name for changed *)
    val (premise_names_for_intro, ctxt_with_counter) =
      case naming_fn_opt of
        SOME naming_fn =>
          let
            (* Use burrow_options to process only changed premises *)
            val names = prems_after_intro
              |> map (fn prem_term => if is_unchanged prem_term then NONE else SOME prem_term)
              |> burrow_options naming_fn
              |> map (fn NONE => SOME "" | SOME name => SOME name)
          in (names, ctxt)
          end
      | NONE =>
          map_premise_counter (fn counter_val =>
            fold_map (fn prem_term => fn current_counter =>
              if is_unchanged prem_term
              then (SOME "", current_counter)  (* Unchanged *)
              else (SOME (assm_name current_counter), current_counter + 1)  (* Changed *)
            ) prems_after_intro counter_val
          ) ctxt

    (* 10. Generate variable names if naming_vars_fn_opt is provided *)
    val (vars_after_intro, _, _) = strip_meta_hhf (fst (Logic.dest_implies (Thm.prop_of st_protected_for_intro)))
    val var_names_for_intro =
      case naming_vars_fn_opt of
        SOME naming_vars_fn =>
          let val names = naming_vars_fn vars_after_intro  (* Call once with all variables *)
          in SOME (map SOME names)
          end
      | NONE => NONE

    (* 11. Call INTRO' with the generated premise names and variable names *)
    val (items_from_intro, (ctxt_after_intro, HHF (st_after_intro, items_after_intro) :: S_after_intro)) =
      INTRO' SINGLE_GOAL NONE var_names_for_intro (SOME premise_names_for_intro)
             (ctxt_with_counter, HHF (st_protected_for_intro, items) :: S)

    (* 12. Unwrap NO_SIMP from the goal conclusion *)
    (* We always wrap once to protect from INTRO *)
    (* If simplify_goal=false, we wrapped twice *)
    val st_final = Conv.gconv_rule (unwrap_goal_conclusion_NO_SIMP ctxt_after_intro) 1 st_after_intro
  in
    (items_from_intro, (ctxt_after_intro, HHF (st_final, items_after_intro) :: S_after_intro))
  end end
  | SIMPLIFY_GOAL_AND_PREMISES' _ _ _ _ _ _ _ _ _ = raise BROKEN_INVARIANT

(* Wrapper that uses premise counter for automatic naming *)
fun SIMPLIFY_GOAL_AND_PREMISES
    simp_facts
    extra_simprocs
    use_system_simps
    premise_names
    simplify_goal
    naming_fn_opt
    naming_vars_fn_opt
    timeout =
  OPR_with_ret (fn s =>
    let val (items, s') = SIMPLIFY_GOAL_AND_PREMISES' simp_facts extra_simprocs use_system_simps premise_names simplify_goal naming_fn_opt naming_vars_fn_opt timeout s
        val _ = report_goal s'
     in (items, s')
    end)

(* Wrapper that parses fact references and uses premise counter *)
fun SIMPLIFY_GOAL_AND_PREMISES''
    raw_simp_facts
    use_system_simps
    premise_names
    simplify_goal =
  OPR (fn (ctxt, SK) =>
    let val simp_facts = maps (Attrib.eval_thms ctxt o single) raw_simp_facts
        val (_, s') = SIMPLIFY_GOAL_AND_PREMISES' simp_facts [] use_system_simps premise_names simplify_goal NONE NONE NONE (ctxt, SK)
        val _ = report_goal s'
     in s'
    end)

(* Command parser for SIMPLIFY operation *)
val SIMPLIFY_CMD =
  let
    val PREMS_CLAUSE = PREMS_KWD |-- Parse.and_list (Scan.repeat1 Parse.name) >> flat
    val WITH_CLAUSE_ONLY = Scan.optional (Parse.$$$ "WITH" |-- Scan.repeat Parse.thm) []

    val parser = PREMS_CLAUSE -- WITH_CLAUSE_ONLY
  in
    parser >> (fn (premise_names, raw_simp_facts) =>
      SIMPLIFY_GOAL_AND_PREMISES''
        raw_simp_facts
        true           (* use_system_simps *)
        premise_names
        false)          (* simplify_goal *)
  end

(** INDUCT & CASE **)

fun powerful_MP ctxt rule thA0 =
  let
    fun protect_prop ctxt ctm = let open Conv
       in case Thm.term_of ctm
           of Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs _ =>
                (arg_conv (abs_conv (protect_prop o snd) ctxt)) ctm
            | Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ =>
                (combination_conv (arg_conv (rewr_conv Thms.prop_def'sym))
                                  (protect_prop ctxt) ctm)
            | _ => Conv.all_conv ctm
      end
    val thA = Conv.fconv_rule (protect_prop ctxt) thA0
  in rule
  |> Conv.fconv_rule (Conv.arg1_conv (protect_prop ctxt))
  |> (Thm.biresolution (SOME ctxt) true [(false, thA)]
        THEN_ALL_NEW Thm.assumption (SOME ctxt)) 1
  |> Seq.pull
  |> (fn SOME (ret, _) => ret
       | NONE => error (String.concat [
            "BUG: CASES' MP\nrule: ", Thm.string_of_thm ctxt rule,
            "\nthA0: ", Thm.string_of_thm ctxt thA0,
            "\nthA (protected): ", Thm.string_of_thm ctxt thA,
            "\nrule (protected): ", Thm.string_of_thm ctxt
              (Conv.fconv_rule (Conv.arg1_conv (protect_prop ctxt)) rule)]))
 end

fun make_case term =
  let val (vars, prems, concl) = strip_meta_hhf term
      val vars' = variant_name_list [] (map fst vars) ~~ map snd vars
      val fixes = map (apfst Binding.name) vars
      val assms = map_index (fn (i, tm) =>
                    ("prem" ^ string_of_int i, [fold_rev Term.abs vars' tm])) prems
      val binds = [((Rule_Cases.case_conclN, 0),
                   SOME (fold_rev Term.abs vars' (HOLogic.dest_Trueprop concl)))]
   in Rule_Cases.Case {
        fixes=fixes, assumes=assms, binds=binds, cases=[]
    }
  end


fun CASES' diff ADDITIONAL_NOTES safe_names smart_rename no_simp tac first_vars (SK as (ctxt0, HHF (st00, items00) :: _)) =
  apply' "Fail to apply the case-split operation."
         (get_reporter()) tac NONE SK
    |> (fn (ctxt, SK as HHF (rule, items0) :: REMAIN_SK) =>
   let val cases0 = Proof_Context.dest_cases (SOME ctxt0) ctxt
                |> filter (fn (_, Rule_Cases.Case {binds,...}) =>
                      forall (fn ((name,_), SOME term) =>
                                    name <> Rule_Cases.case_conclN orelse
                                    (case term of Const(\<^const_name>\<open>HOL.induct_true\<close>, _) => false
                                                | Const(\<^const_name>\<open>HOL.True\<close>, _) => false
                                                | _ => true)
                               | _ => true) binds)
       val diffxxx = (num_goals_of' rule - num_goals_of' st00 + 1 + diff) - length cases0
       val cases =
               if diffxxx = 0
               then cases0
               else if diffxxx > 0
               then let
                    val additional = drop (length cases0) (goals_of' rule)
                                  |> map_index (fn (i,x) =>
                                        ("Prem" ^ string_of_int i, make_case x))
                 in cases0 @ additional
                end
               else error "BUG REWLK"
       val used_qualifiers = quanlifiers_of (print_stack SK)
       val cases = variant_name_list used_qualifiers (map #1 cases)
                ~~ map #2 cases

       fun is_case x t =
            x = Rule_Cases.case_conclN andalso not (Term.exists_subterm Term.is_Var t)
       fun goal_term_of ctxt binds =
            if exists (fn ((x, _), SOME t) => is_case x t | _ => false) binds
            then Vartab.lookup (Variable.binds_of ctxt) (Rule_Cases.case_conclN, 0)
                  |> (fn SOME (\<^Type>\<open>bool\<close>, goal) => HOLogic.mk_Trueprop goal
                       | _ => error "BUG 0ejOD0qNRfaTJCrbK7lH3w")
            else fst (Logic.dest_implies (Thm.prop_of st00))

       (*TODO: consider the
            `Conv.gconv_rule (Simplifier.full_rewrite (ctxt addsimps simp_thms)) 1 goalx`
          in case of the high_auto_mode.
          We need a preplay to get the shape of the goals.*)
       val siblings = map (fn (_, kase as Rule_Cases.Case {fixes, binds, ...}) =>
              let val (asms, ctxt) = Proof_Context.apply_case kase ctxt
               in PROP ((map (apfst Binding.name_of) fixes, flatten_facts asms), goal_term_of ctxt binds)
              end
            ) cases

       fun CB initial rule cases siblings
              ctxt' (lem, _, SK, param) =
        let val rule' =
                if initial then rule
                else let val thA = lem
                                |> is_protected (Thm.prop_of lem) ? Goal.conclude
                                |> singleton (Proof_Context.export ctxt' ctxt)
                  in thA
                  |> not initial ? ( powerful_MP ctxt rule
                                  #> not (null cases) ? conclude_goal )
                 end
         in case cases
         of [] =>
            (ctxt, HHF (rule', items0) :: SK)
          | ((name, kase) :: remaining_cases) =>
        let val opt_case_name = case param of CASE_NAME param => param
                                            | NO_PARAM => NONE
                                            | _ => raise BROKEN_INVARIANT
            (* val name = if Char.isAlpha (String.sub (name, 0)) then name
                       else "case_" ^ name *)
            val kase = case kase
                  of Rule_Cases.Case {fixes, assumes, binds, cases} =>
                     Rule_Cases.Case {
                       fixes = (
                         case opt_case_name
                           of SOME fixes'0 =>
                              let val fixes' = if member (op =) ["COMPLETE_NEXT", "RELAXED"]
                                                                 (Config.get ctxt working_mode)
                                               then take (length fixes) fixes'0
                                               else fixes'0
                               in map2_opt (fn NONE => I
                                             | SOME name => fn (_, T) => (Binding.name name, T)
                                           ) fixes' fixes
                                  handle ListPair.UnequalLengths =>
                                      raise OPR_FAIL (INVALID_OPR, "Incorrect number of VARS")
                              end
                            | _ =>
                              let val fixes0 = case smart_rename of
                                      SOME (tgt_name, tgt_type) =>
                                        if length (filter (fn (_, T) => T = tgt_type) fixes) = 1
                                           andalso not (exists (fn (B, _) =>
                                                    Binding.name_of B = tgt_name) fixes)
                                        then map (fn (B, T) =>
                                          if T = tgt_type
                                          then (Binding.name tgt_name, T)
                                          else (B, T)) fixes
                                        else fixes
                                    | NONE => fixes
                               in fold_map (fn (B,T) => fn names =>
                                    let val name = Binding.name_of B
                                        val name = if Name.is_internal name then Name.dest_internal name
                                                                            else name
                                        val (name, names) =
                                          if Config.get ctxt deconflict_case_fixes
                                             andalso not (member (op =) safe_names name)
                                          then variant_name name names
                                          else (name, names)
                                     in ((Binding.name name,T), names)
                                    end ) fixes0 (Variable.names_of ctxt)
                                  |> #1
                              end ),
                       assumes = map_index (fn (i,(N,tms)) =>
                                    if N = "" then ("prem" ^ string_of_int i, tms)
                                              else (N, tms) ) assumes,
                       binds=binds,
                       cases=cases
                     }

            val Rule_Cases.Case {fixes, cases, binds, ...} = kase
            val _ = if null cases then () else error "XQY: Unsupported! #1"

            
            val (asms, ctxt) = Proof_Context.apply_case kase ctxt

            val goalx =
               (if exists (fn ((x, _), SOME t) => is_case x t | _ => false) binds
                then Vartab.lookup (Variable.binds_of ctxt) (Rule_Cases.case_conclN, 0)
                  |> (fn SOME (\<^Type>\<open>bool\<close>, goal) => HOLogic.mk_Trueprop goal
                       | _ => error "BUG 0ejOD0qNRfaTJCrbK7lH3w")
                  |> Thm.cterm_of ctxt
                else Thm.cprop_of st00
                  |> Thm.dest_arg1)
                  |> Goal.init

            val binding = Binding.name (variant_factname ctxt name)
            val bindings = map (rpair [] o Binding.qualify_name true binding o fst) asms

            fun export is_G asms =
                let val (A,B) = Assumption.assume_export is_G asms
                 in (A #> Thm.permute_prems 0 (length asms) ,B)
                end
         in ctxt
         |> fold_burrow ( Assumption.add_assms export
                        o map (Thm.cterm_of ctxt) ) (map #2 asms)
         |-> (fn thms => fn ctxt =>
           let val tagged = maps (filter (is_tagged_Trueprop o Thm.prop_of)) thms
               val thms  = map ( filter_out (is_tagged_Trueprop o Thm.prop_of)
                              #> map (unwrap_tags ctxt) ) thms
               val pairs = bindings ~~ thms
               val notes = pairs
                        |> filter_out (null o snd)
                        |> map (apsnd (map (fn th => ([remove_TAG_premises ctxt th], []))))
            in ctxt
            |> not (null pairs) ?
               ( Proof_Context.note_thms "" ((binding,[]), [(maps snd pairs,[])]) #> snd)
            |> Proof_Context.note_thmss "" (ADDITIONAL_NOTES ctxt tagged @ notes)
           end )
         |> (fn (thms0, ctxt) =>
        let val thms = map (apfst simp_fact_name') thms0
            val goalx =
              if Config.get ctxt high_auto_mode andalso not no_simp
              then let
                   val simp_thms = maps snd thms
                in if null simp_thms
                 then goalx
                 else Conv.gconv_rule (Simplifier.full_rewrite (ctxt addsimps simp_thms)) 1 goalx
               end
              else goalx
            val items' = ( map (apfst Binding.name_of) fixes,
                           map (apsnd (map Thm.prop_of)) thms
                             |> flatten_facts )
            val report = get_reporter ()
            fun PRT _ T = case siblings
                            of [_] => cat_tree T (print_stack [HHF (st00, items00)])
                             | _ => cat_tree (BUNDL (empty_items, T :: tl siblings))
                                             (print_stack [HHF (st00, items00)])
         in report (New_Items items')
          ; report (Consider_Case (Binding.name_of binding, items'))
          ; if null remaining_cases
         then (ctxt, ( HHF (goalx, items')
                 :: MAGIC (CB false rule' remaining_cases (tl siblings), PRT, NO_PARAM)
                 :: SK))
         else (ctxt, ( HHF (goalx, items')
                 :: ENDBLK T_NXT
                 :: MAGIC (CB false rule' remaining_cases (tl siblings), PRT, NO_PARAM)
                 :: SK))
        end )
        end
        end
    in CB true rule cases siblings
          ctxt (Drule.dummy_thm, ([],[]), REMAIN_SK, CASE_NAME first_vars)
   end
     | _ => raise BROKEN_INVARIANT)
  | CASES' _ _ _ _ _ _ _ _ = raise BROKEN_INVARIANT

(* Syntax *)



exception IH_MAP of (string * string list) list

(* Auto-insert mechanism for induction (previously named induct_auto_use_facts).
 * When enabled, local facts mentioning "dirty" free variables (those being
 * inducted on or generalized) are automatically collected, wrapped via
 * TAG + conjunction, and passed through the induction tactic's more_facts
 * path — where Method.insert_tac inserts them as goal premises that get
 * generalized along with the arbitrary variables. After induction, the
 * wrapped conjunction is unpacked and restored as named local facts in
 * each case's context (see update_tampered below).
 *
 * The legacy name `induct_auto_use_facts` is a misnomer: no "using" role
 * is performed — the facts always flow through insertion. *)
val induct_auto_insert_facts = Attrib.setup_config_bool \<^binding>\<open>induct_auto_insert_facts\<close> (K false)

(* Policy for how INDUCT / CASE_SPLIT check the user's `using` facts
 * against the picked rule's `consumes` count.
 *
 *   "require" (default) : |using| < consumes → error.
 *                         |using| > consumes → extras flow to insertion.
 *                         Forces the user to supply enough facts to
 *                         discharge the rule's major premises.
 *
 *   "subgoals"          : |using| < consumes → unconsumed premises
 *                         become extra subgoals (Isabelle's native
 *                         Rule_Cases.consume + internalize behavior).
 *                         |using| > consumes → extras flow to insertion.
 *                         NOTE: if `arbitrary:` variables are requested
 *                         alongside |using| < consumes, Isabelle's
 *                         `arbitrary_tac` silently skips the
 *                         generalization (the inflated `k` walks past
 *                         the end of the goal conclusion). A warning is
 *                         emitted to the reporter when this combination
 *                         is detected.
 *
 *   "strict"            : |using| ≠ consumes → error. Both directions
 *                         rejected; user must match the count exactly.
 *)
val consumes_policy = Attrib.setup_config_string
      \<^binding>\<open>consumes_policy\<close> (K "require")

fun parse_consumes_policy s =
  case s of
    "require" => ("require" : string)
  | "subgoals" => "subgoals"
  | "strict" => "strict"
  | _ => error ("Invalid `consumes_policy`: `" ^ s ^
                "`. Expected one of `require`, `subgoals`, `strict`.");

(* ========================================================================
 * ISABELLE VERSION SYNC REQUIRED ON UPGRADE
 * ========================================================================
 * The helpers below (align_left, align_right, prep_inst, special_rename_params,
 * get_inductP_local, mk_inst_rule, get_casesT_local, get_casesP_local,
 * mk_inst_cases_rule) are verbatim copies of private functions from
 *   contrib/Isabelle2024/src/Tools/induct.ML
 *
 * They exist so that pick_induct_rule / pick_case_split_rule can replicate
 * Isabelle's rule-discovery logic without modifying the system induction
 * tactic. The picked rule is then passed to Isabelle's induction_tac as
 * opt_rule = SOME [picked_rule], forcing Isabelle to use exactly the rule
 * we pre-analyzed.
 *
 * Last synced with: Isabelle2024
 * When upgrading Isabelle, verify these are still correct by diffing:
 *   - contrib/Isabelle2024/src/Tools/induct.ML:
 *     align_left/align_right (lines 401-407),
 *     prep_inst (line 412),
 *     special_rename_params (line 633),
 *     get_inductP (line 754),
 *     get_casesP/get_casesT (lines 485-488),
 *     inst_rule inside gen_induct_context_tactic (line 763),
 *     inst_rule inside cases_context_tactic (line 496).
 *   - contrib/Isabelle2024/src/Pure/Isar/rule_cases.ML:
 *     consume (line 198), get_consumes.
 *
 * Symptom of missed sync: analyze_induct / analyze_case_split reports a
 * stale rule; consume-fact validation fires on the wrong rule; subtle
 * divergence between analysis and execution.
 * ======================================================================== *)

(* Aligned pairing — copied from induct.ML (lines 401-407, private). *)
fun ind_align_left msg xs ys =
  let val m = length xs and n = length ys
  in if m < n then error msg else (take n xs ~~ ys) end;

fun ind_align_right msg xs ys =
  let val m = length xs and n = length ys
  in if m < n then error msg else (drop (m - n) xs ~~ ys) end;

(* Instantiation preparation — copied from induct.ML (line 412, private). *)
fun ind_prep_inst ctxt align tune (tm, ts) =
  let
    fun prep_var (Var (x, xT), SOME t) =
          let
            val ct = Thm.cterm_of ctxt (tune t);
            val tT = Thm.typ_of_cterm ct;
          in
            if Type.could_unify (tT, xT) then SOME (x, ct)
            else error (Pretty.string_of (Pretty.block
             [Pretty.str "Ill-typed instantiation:", Pretty.fbrk,
              Syntax.pretty_term ctxt (Thm.term_of ct), Pretty.str " ::", Pretty.brk 1,
              Syntax.pretty_typ ctxt tT]))
          end
      | prep_var (_, NONE) = NONE;
    val xs = Induct.vars_of tm;
  in
    align "Rule has fewer variables than instantiations given" xs ts
    |> map_filter prep_var
  end;

(* Induct-predicate rule lookup — copied from induct.ML (line 754, private). *)
fun ind_get_inductP ctxt (fact :: _) = map single (Induct.find_inductP ctxt (Thm.concl_of fact))
  | ind_get_inductP _ _ = [];

(* Cases rule lookups — copied from induct.ML (lines 485-489, private). *)
fun ind_get_casesT ctxt ((SOME t :: _) :: _) = Induct.find_casesT ctxt (Term.fastype_of t)
  | ind_get_casesT _ _ = [];

fun ind_get_casesP ctxt (fact :: _) = Induct.find_casesP ctxt (Thm.concl_of fact)
  | ind_get_casesP _ _ = [];

(* Special parameter renaming for type-induction with a single Free target.
 * Copied from induct.ML (line 633, private). *)
fun ind_special_rename_params ctxt [[SOME (Free (z, Type (T, _)))]] [thm] =
      let
        val x = Name.clean (Variable.revert_fixed ctxt z);
        fun index _ [] = []
          | index i (y :: ys) =
              if x = y then x ^ string_of_int i :: index (i + 1) ys
              else y :: index i ys;
        fun rename_params [] = []
          | rename_params ((y, Type (U, _)) :: ys) =
              (if U = T then x else y) :: rename_params ys
          | rename_params ((y, _) :: ys) = y :: rename_params ys;
        fun rename_asm A =
          let
            val xs = rename_params (Logic.strip_params A);
            val xs' =
              (case filter (fn x' => x' = x) xs of
                [] => xs
              | [_] => xs
              | _ => index 1 xs);
          in Logic.list_rename_params xs' A end;
        fun rename_prop prop =
          let val (As, C) = Logic.strip_horn prop
          in Logic.list_implies (map rename_asm As, C) end;
        val thm' = Thm.renamed_prop (rename_prop (Thm.prop_of thm)) thm;
      in [Rule_Cases.save thm thm'] end
  | ind_special_rename_params _ _ ths = ths;

(* Inst_rule for INDUCTION — derived from induct.ML:763 (inside gen_induct_context_tactic).
 * Returns ((cases, consumes), instantiated_thm) — the same shape that
 * Isabelle's ruleq produces. We discard mod_cases here because our agent
 * uses the rule only for consumes + premise display; the actual tactic
 * run (with opt_rule = SOME [picked]) re-applies IH-naming mod_cases
 * inside induction_tac. *)
fun mk_induct_inst_rule ctxt insts (concls, r) =
  (if null insts then `Rule_Cases.get r
   else (ind_align_left "Rule has fewer conclusions than arguments given"
          (map Logic.strip_imp_concl (Logic.dest_conjunctions (Thm.concl_of r))) insts
        |> maps (ind_prep_inst ctxt ind_align_right (Induct.atomize_term ctxt))
        |> infer_instantiate ctxt) r |> pair (Rule_Cases.get r));

(* Inst_rule for CASE_SPLIT — derived from induct.ML:496 (inside cases_context_tactic).
 * Note the different alignment and argument structure. *)
fun mk_cases_inst_rule ctxt insts r =
  (if null insts then r
   else
     (ind_align_left "Rule has fewer premises than arguments given" (Thm.prems_of r) insts
       |> maps (ind_prep_inst ctxt ind_align_left I)
       |> infer_instantiate ctxt) r)
  |> pair (Rule_Cases.get r);

(* Pick the induction rule that Isabelle's induction_tac would pick first
 * (modulo fall-through on downstream failures, which the simpler pre-pick
 * approach does not preserve). Returns (raw_rule, (cases_info, consumes, inst_thm))
 * — the raw_rule is what to pass as opt_rule to Isabelle; the inst_thm
 * carries the post-inst_rule premises for user display. *)
fun pick_induct_rule ctxt opt_rule insts facts =
  let
    (* Skip candidates that fail inst_rule so the next is tried, matching
     * Isabelle's `Seq.try inst_rule` fall-through. *)
    val try_inst_rule = try (mk_induct_inst_rule ctxt insts)
  in
    case opt_rule of
      SOME rs =>
        (case try (Rule_Cases.strict_mutual_rule ctxt) rs of
           NONE => NONE
         | SOME mr =>
             (case try_inst_rule mr of
                NONE => NONE
              | SOME result => SOME (#2 mr, result)))
    | NONE =>
        let
          val candidates =
            ind_get_inductP ctxt facts @
            map (ind_special_rename_params ctxt insts) (Induct.get_inductT ctxt insts)
          val mutuals = map_filter (Rule_Cases.mutual_rule ctxt) candidates
          fun find [] = NONE
            | find (pair :: rest) =
                (case try_inst_rule pair of
                   NONE => find rest
                 | SOME result => SOME (#2 pair, result))
        in find mutuals end
  end;

(* Pick the case-split rule. Mirrors pick_induct_rule but for cases_context_tactic. *)
fun pick_case_split_rule ctxt opt_rule insts facts =
  let
    (* Skip candidates that fail inst_rule — same fall-through idiom as
     * pick_induct_rule. *)
    val try_inst = try (mk_cases_inst_rule ctxt insts)
    (* Mimic cases_context_tactic's logic that bumps the first fact into
     * opt_rule if its concl is an elim-rule conclusion. *)
    val (opt_rule', facts') =
      (case (opt_rule, facts) of
        (NONE, th :: ths) =>
          if is_some (Object_Logic.elim_concl ctxt th) then (SOME th, ths)
          else (opt_rule, facts)
      | _ => (opt_rule, facts));
  in
    case opt_rule' of
      SOME r =>
        (case try_inst r of
           NONE => NONE
         | SOME result => SOME (r, result))
    | NONE =>
        let
          val candidates =
            ind_get_casesP ctxt facts' @ ind_get_casesT ctxt insts
          fun find [] = NONE
            | find (r :: rest) =
                (case try_inst r of
                   NONE => find rest
                 | SOME result => SOME (r, result))
        in find candidates end
  end;

(* Structure-side type declarations matching the signature. SML requires
 * the structure to repeat concrete `type t = ty` bindings even when the
 * signature already specifies them. *)
type induct_facts = {using: thm list, insertion: (string * thm list) list}
type induct_analysis =
  {rule: thm,
   rule_name: string option,
   consumes: int,
   consume_premises: term list,
   remaining_premises: term list}

(* Strip `def_insts` (used by INDUCT) down to term-only `insts` needed by
 * the rule-picker. We deliberately do NOT run `Induct.add_defs` here —
 * that function has context side effects (Local_Defs.define) that would
 * duplicate when INDUCT' subsequently runs `induction_tac`.
 *
 * For rule discovery and inst_rule, only the term-level view of insts
 * matters: `get_inductT` looks at the type of the last term, and
 * `inst_rule` uses `vars_of` on the rule's conclusion to pair up with
 * instantiation terms. The binding-name and `do_def` flag are irrelevant
 * at the picker/analyze layer. *)
fun strip_def_insts def_insts =
  map (map (fn NONE => NONE | SOME (_, (t, _)) => SOME t)) def_insts;

(* Build an `induct_analysis` record from a rule-pick result.
 * `consumes` is taken from the `Rule_Cases.get`-derived tuple so it
 * reflects the RAW theorem's tag (instantiation may discard tags).
 * `rule_name` similarly comes from the raw theorem's name hint. *)
fun mk_analysis (raw_rule, consumes_n, inst_thm) : induct_analysis =
  let
    val prems = Thm.prems_of inst_thm
    val name_final =
      if Thm.has_name_hint raw_rule
      then let val s = Thm.get_name_hint raw_rule
           in if s = "" then NONE else SOME s end
      else NONE
  in
    {rule = inst_thm,
     rule_name = name_final,
     consumes = consumes_n,
     consume_premises = take consumes_n prems,
     remaining_premises = drop consumes_n prems}
  end;

(* analyze_induct: pre-execution pick-and-report for INDUCT. Returns NONE
 * if no candidate rule instantiates successfully. The `facts` argument is
 * used only for predicate-rule discovery (get_inductP looks at the first
 * fact's conclusion). *)
fun analyze_induct ctxt (_, (def_insts, ((_, _), opt_rule))) facts =
  case pick_induct_rule ctxt opt_rule (strip_def_insts def_insts) facts of
    NONE => NONE
  | SOME (raw_rule, ((_, consumes_n), inst_thm)) =>
      SOME (mk_analysis (raw_rule, consumes_n, inst_thm));

(* analyze_case_split: pre-execution pick-and-report for CASE_SPLIT. *)
fun analyze_case_split ctxt (_, (insts, opt_rule)) facts =
  case pick_case_split_rule ctxt opt_rule insts facts of
    NONE => NONE
  | SOME (raw_rule, ((_, consumes_n), inst_thm)) =>
      SOME (mk_analysis (raw_rule, consumes_n, inst_thm));

(* Shared consumes-count validation for INDUCT'/CASE_SPLIT'. Raises
 * OPR_FAIL on policy violation. Returns unit on success (the caller
 * proceeds to tactic execution).
 *
 *   kind_str       : "Induction" or "Case-split" (error-message prefix)
 *   rule_name_str  : picked rule's name, for error messages
 *   consumes_n     : rule's consumes count (0 when no rule was picked)
 *   u              : |using|
 *   arbitrary      : arbitrary-var list (INDUCT only; [] for CASE_SPLIT)
 *                    — used to emit an extra warning under `"subgoals"`
 *                    policy when combined with |using| < consumes
 *   inst_thm_opt   : the post-inst_rule theorem for the picked rule
 *                    (SOME thm when analysis succeeded, NONE otherwise).
 *                    Needed under `"subgoals"` to inspect unconsumed
 *                    premises for schematic variables.
 *)
fun validate_consumes ctxt
      {kind_str, rule_name_str, consumes_n, u, arbitrary, inst_thm_opt} =
  let val policy = parse_consumes_policy (Config.get ctxt consumes_policy) in
  case policy of
    "require" =>
      if u < consumes_n then
        raise OPR_FAIL (INVALID_OPR,
          kind_str ^ " rule `" ^ rule_name_str ^ "` requires " ^
          string_of_int consumes_n ^ " `using` fact(s) to discharge its \
          \major premise(s), but only " ^ string_of_int u ^ " were \
          \provided. (policy = `require`; set `consumes_policy` to \
          \`subgoals` to allow unconsumed premises to appear as \
          \subgoals instead.)")
      else ()
  | "subgoals" =>
      if u < consumes_n then
        let
          (* Unconsumed premises after inst_rule (post-pick). Reject if
           * any contains schematic variables — Minilang's CASES' does
           * not handle subgoals with schematics well. *)
          val unconsumed =
            case inst_thm_opt of
              NONE => []
            | SOME thm => drop u (take consumes_n (Thm.prems_of thm))
          val schematic_vars =
            fold Term.add_vars unconsumed []
            |> map (Term.string_of_vname o #1)
            |> distinct (op =)
          val _ =
            if null schematic_vars then ()
            else raise OPR_FAIL (INVALID_OPR,
              "Schematic variable" ^
              (if length schematic_vars = 1 then " " else "s ") ^
              String.concatWith ", " schematic_vars ^
              " must be instantiated.")
        in
          if exists (not o null) arbitrary
          then writeln
            "warning: `consumes_policy = subgoals` with |using| < \
            \consumes and a non-empty `arbitrary` clause: Isabelle's \
            \arbitrary_tac may silently skip the generalization."
          else ()
        end
      else ()
  | "strict" =>
      if u <> consumes_n then
        raise OPR_FAIL (INVALID_OPR,
          kind_str ^ " rule `" ^ rule_name_str ^ "` consumes " ^
          string_of_int consumes_n ^ " fact(s), but " ^
          string_of_int u ^ " were provided as `using`. (policy = \
          \`strict`; set `consumes_policy` to `require` or `subgoals` \
          \to relax this check.)")
      else ()
  | _ => ()   (* parse_consumes_policy already rejected invalid values *)
  end;

fun INDUCT' (no_simp, (insts, ((arbitrary, taking), opt_rule))) first_vars
            ({using, insertion} : induct_facts)
            (ctxt, SK) =
  let
      (* Pre-execution: pick the rule that will be used and validate that
       * the user supplied enough `using` facts to discharge its major
       * premises. When opt_rule = NONE, force Isabelle to use exactly our
       * picked rule (opt_rule = SOME [raw_rule]), so execution matches
       * analysis. We pass the RAW (pre-inst_rule) theorem so Isabelle's
       * own inst_rule does the instantiation normally — passing the
       * already-instantiated thm would confuse its re-instantiation. *)
      val pick_result =
        pick_induct_rule ctxt opt_rule (strip_def_insts insts) using
      val (effective_opt_rule, consumes_n, rule_name_str, inst_thm_opt) =
        case pick_result of
          NONE =>
            (* No rule found. Fall through to induction_tac with user's
             * opt_rule — it will produce a proper error itself. *)
            (opt_rule, 0, "<no rule found>", NONE)
        | SOME (raw_rule, ((_, consumes_n), inst_thm)) =>
            let val name_str =
                  if Thm.has_name_hint raw_rule
                  then Thm.get_name_hint raw_rule
                  else "<auto-picked rule>"
                val forced_rule =
                  case opt_rule of
                    SOME _ => opt_rule   (* user explicit — keep as-is *)
                  | NONE => SOME [raw_rule]
            in (forced_rule, consumes_n, name_str, SOME inst_thm) end

      val u = length using
      val _ = validate_consumes ctxt
                {kind_str = "Induction", rule_name_str = rule_name_str,
                 consumes_n = consumes_n, u = u,
                 arbitrary = arbitrary, inst_thm_opt = inst_thm_opt}

      (* Under `subgoals` policy with |using| < consumes: lower the rule's
       * `consumes` tag to `u` so Isabelle's internalize atomizes only the
       * premises actually discharged by `using`. Remaining premises stay
       * as ordinary rule premises, which resolve_tac turns into `Prem<i>`
       * subgoals (handled by CASES'). Without this, internalize would
       * atomize the unconsumed premise into the rule's conclusion (via
       * `premise ⟶ concl`), making resolve fail on concrete goals whose
       * shape doesn't include a matching HOL implication. *)
      val effective_opt_rule =
        if Config.get ctxt consumes_policy = "subgoals" andalso u < consumes_n
        then case effective_opt_rule of
               SOME rules => SOME (map (Rule_Cases.put_consumes (SOME u)) rules)
             | NONE => NONE
        else effective_opt_rule

      (* Dirty-var set — free variables of the induction targets ∪
       * `arbitrary` vars. A thm in an insertion fact is "dirty" iff
       * its prop mentions at least one of these as a Free — i.e. the
       * thm will be affected by generalization. Shared by both
       * auto-insert (scans context) and explicit insertion (agent
       * `facts_to_generalize`). *)
      val dirty_frees = fold (fold (fn NONE => I
                                     | SOME (_, (X, _)) => Term.add_frees X)) insts []
                     |> fold (curry (merge (op =))) arbitrary
      val dirty = member (op =) dirty_frees
      fun mark_dirty th =
        (Term.exists_subterm (fn Free f => dirty f | _ => false) (Thm.prop_of th), th)

      (* Explicit insertion from callers (e.g. agent `facts_to_generalize`).
       * Already carries name ↔ thm list pairing. Each thm gets a
       * per-thm dirty bit; facts with zero dirty thms are dropped
       * (they would contribute nothing to the TAG conjunction). *)
      val explicit_tamper =
        map (apsnd (map mark_dirty)) insertion
        |> filter (exists fst o snd)
      val dropped_insertion =
        filter_out (member (op =) (map fst explicit_tamper)) (map fst insertion)
      val _ = if null dropped_insertion then ()
              else get_reporter () (Internal (DROPPED_INSERTION_FACTS dropped_insertion))
      val explicit_names = map fst explicit_tamper
      val explicit_fact' =
        maps (map_filter (fn (true, x) => SOME x | _ => NONE) o snd) explicit_tamper

      (* Auto-insert: scan leading goal's local facts and mark dirty.
       * Merge strategy: explicit wins — auto entries sharing a name
       * with any explicit entry are dropped so we never double-wrap
       * the same fact. *)
      val (auto_tamper, auto_fact') =
        if Config.get ctxt induct_auto_insert_facts
        then let
            val ((_, facts), _) = context_of_leading_goal (print_stack SK)
            val facts = map (fn (name, _) => (name, Proof_Context.get_thms ctxt name)) facts
            val tf = map (apsnd (map mark_dirty)) facts
                  |> filter (exists fst o snd)
                  |> filter_out (fn (n, _) => member (op =) explicit_names n)
         in (tf, maps (map_filter (fn (true, x) => SOME x | _ => NONE) o snd) tf)
        end
        else ([], [])

      val tamper_facts = auto_tamper @ explicit_tamper
      val tamper_fact' = auto_fact' @ explicit_fact'

      val IH_map = Unsynchronized.ref []
      val diff = case effective_opt_rule of NONE => 0
                    | SOME rules => length rules - 1
      (* `wrapped` is the single TAG+conjI-packed thm (empty list if
       * there are no dirty insertion atoms). It is inserted into the
       * goal via a DEDICATED `Method.insert_tac` call BEFORE
       * induction_tac runs, so `Rule_Cases.consume` inside
       * induction_tac never sees it. induction_tac receives only
       * `using`; its arbitrary_tac will still generalize the inserted
       * wrapped premise because it is now part of the goal. Post-
       * induction, the tagged wrapped premise surfaces in each case's
       * assumptions, gets filtered out by CASES' (is_tagged_Trueprop)
       * and routed to `update_tampered` for named restoration. *)
      fun tac (ctxt, st) =
        let val st' = pop_n_goals (diff + 1) st
            val wrapped =
              if null tamper_fact' then [] else [wraps ctxt tamper_fact']
            (* `Method.insert_tac ... 1 : tactic` returns thm Seq.seq;
             * `induction_tac ... 1 : context_tactic` takes
             * (ctxt, st) and returns context_state Seq.result Seq.seq.
             * Seq.maps chains them: for each st'' produced by
             * insert_tac, run induction_tac in the same context. *)
         in Seq.maps (fn st'' =>
              induction_tac IH_map (not no_simp) insts arbitrary taking
                            effective_opt_rule using 1 (ctxt, st''))
             (Method.insert_tac ctxt wrapped 1 st')
        end

      fun update_tampered ctxt th =
        let val ths = unwrap_conjs ctxt th
                   |> map (unwrap_tags ctxt)
            fun burrow' [] _ = []
              | burrow' ((true , _ ) :: L) (th::ths) = th :: burrow' L ths
              | burrow' ((false, th) :: L) (    ths) = th :: burrow' L ths
              | burrow' _ _ = error "BUG"
            fun burrow'2 [] ths = ths
              | burrow'2 ((true , _) :: L) (_ ::ths) = burrow'2 L ths
              | burrow'2 ((false, _) :: L) (    ths) = burrow'2 L ths
              | burrow'2 _ _ = error "BUG"
            fun burrow [] [] = []
              | burrow ((N, L) :: L') ths = (N, burrow' L ths) :: burrow L' (burrow'2 L ths)
              | burrow _ _ = error "BUG"
            val tamper_facts'' = burrow tamper_facts ths
         in map (fn (B,ths) => ((mk_binding B, []), [(ths,[])]) ) tamper_facts''
        end
      val induct_safe_names =
            fold (fold (fn NONE => I
                         | SOME (_, (X, _)) =>
                             fold (insert (op =) o Variable.revert_fixed ctxt o fst)
                                  (Term.add_frees X [])))
                 insts []
      val smart_rename =
            case insts of
              [[SOME (_, (Free (n, T), _))]] =>
                SOME (Variable.revert_fixed ctxt n, T)
            | _ => NONE
      val ret = CASES' diff (maps o update_tampered) induct_safe_names smart_rename no_simp tac first_vars (ctxt, SK)
   in get_reporter () (Internal (IH_MAP (!IH_map)))
    ; ret
  end

fun CASE_SPLIT' (no_simp, (insts, opt_rule)) vars (using : thm list) (ctxt, SK) =
  let
      (* Pre-execution: pick the case-split rule and validate that the user
       * supplied enough `using` facts to discharge its major premises.
       * As in INDUCT', we pass the RAW theorem (pre-inst_rule) so that
       * Isabelle's cases_context_tactic does the instantiation normally. *)
      val pick_result = pick_case_split_rule ctxt opt_rule insts using
      val (effective_opt_rule, consumes_n, rule_name_str, inst_thm_opt) =
        case pick_result of
          NONE => (opt_rule, 0, "<no rule found>", NONE)
        | SOME (raw_rule, ((_, consumes_n), inst_thm)) =>
            let val name_str =
                  if Thm.has_name_hint raw_rule
                  then Thm.get_name_hint raw_rule
                  else "<auto-picked rule>"
                val forced_rule =
                  case opt_rule of
                    SOME _ => opt_rule
                  | NONE => SOME raw_rule
            in (forced_rule, consumes_n, name_str, SOME inst_thm) end

      val u = length using
      val _ = validate_consumes ctxt
                {kind_str = "Case-split", rule_name_str = rule_name_str,
                 consumes_n = consumes_n, u = u,
                 arbitrary = [], inst_thm_opt = inst_thm_opt}

      (* Under `subgoals` policy with |using| < consumes: lower the rule's
       * `consumes` tag so cases_context_tactic leaves the remaining
       * premises as ordinary Prem<i> subgoals. See INDUCT' for rationale. *)
      val effective_opt_rule =
        if Config.get ctxt consumes_policy = "subgoals" andalso u < consumes_n
        then case effective_opt_rule of
               SOME rule => SOME (Rule_Cases.put_consumes (SOME u) rule)
             | NONE => NONE
        else effective_opt_rule

      val tac = Induct.cases_context_tactic (not no_simp) insts effective_opt_rule using 1
   in CASES' 0 (K (K [])) [] NONE no_simp tac vars (ctxt, SK)
  end

val INDUCT = timed_OPR 10 ooo INDUCT'
fun INDUCT'' (args, vars, raw_using) s =
  let val ctxt = context_of s
      val toks = if \<^try>\<open>Token.is_eof (List.last args) catch _ => false\<close>
                 then args
                 else args @ [Token.eof]
      val (args', _) = ind_synt (Context.Proof ctxt) toks
      val using = Attrib.eval_thms ctxt raw_using
   in timed_OPR 10 (INDUCT' args' vars {using = using, insertion = []}) s
  end
val INDUCT_CMD = CONTEXTUAL_CMD (fn ctxt =>
         ind_synt (Context.Proof ctxt) -- OPT_VARS -- Scan.optional WITH_CLAUSE []
      >> (fn (((no_simp, (insts, ((arbitrary, taking), opt_rule))), vars), raw_using) =>
        let val using = Attrib.eval_thms ctxt raw_using
         in INDUCT (no_simp, (insts, ((arbitrary, taking), opt_rule))) vars
              {using = using, insertion = []}
        end ))

val CASE_SPLIT = timed_OPR 10 ooo CASE_SPLIT'
val CASE_SPLIT_CMD = CONTEXTUAL_CMD (fn ctxt =>
         case_synt (Context.Proof ctxt) -- OPT_VARS -- Scan.optional WITH_CLAUSE []
      >> (fn (((no_simp, (insts, opt_rule)), vars), raw_facts) =>
        let val facts = Attrib.eval_thms ctxt raw_facts
         in CASE_SPLIT (no_simp, (insts, opt_rule)) vars facts
        end ) )
fun CASE_SPLIT'' (args, vars, raw_facts) s =
  let val ctxt = context_of s
      val toks = if \<^try>\<open>Token.is_eof (List.last args) catch _ => false\<close>
                 then args
                 else args @ [Token.eof]
      val (args', _) = case_synt (Context.Proof ctxt) toks
      val facts = Attrib.eval_thms ctxt raw_facts
   in timed_OPR 10 (CASE_SPLIT' args' vars facts) s
  end


(** RULE **)

fun RULE' [] raw_facts (SK as (ctxt, _)) =
    let val facts = Attrib.eval_thms ctxt raw_facts
     in apply' "Fail to apply the rule." (get_reporter())
               (CONTEXT_TACTIC (Classical.standard_tac (#1 SK) facts)) NONE SK
    end
 (* if NEED_STANDARD SK
    then TRY_STANDARD SK
    else let val facts = Attrib.eval_thms ctxt raw_facts
     in RULE'_i [] facts SK
    end *)
  | RULE' raw_rules raw_facts (ctxt, HHF (st, items) :: SK) =
    let val facts = Attrib.eval_thms ctxt raw_facts

        fun transpose [] [] = []
          | transpose nxt [] = transpose [] (rev nxt)
          | transpose nxt ([] :: L) = transpose nxt L
          | transpose nxt ((x :: L) :: L') = x :: transpose (L :: nxt) L'
        val rules = maps (fn raw_rule =>
              let val name = name_of_ref (fst raw_rule)
               in map (fn rule0 =>
                    let open Phi_Sledgehammer_Solver
                        val rule = rule0 OF facts
                        fun try_drule rule =
                         (case try Tactic.make_elim rule
                            of SOME rule' => [(true, rule')]
                             | NONE => [])
                     in case infer_type_of_rule name rule
                     of T_ELIM => [(true, rule)]
                      | T_DEST => (case try Tactic.make_elim rule
                                     of SOME rule => [(true, rule)]
                                      | NONE      => [(false, rule)])
                      | T_UNKNOWN =>
                            if Thm.nprems_of rule = 1
                            then [(false, rule)] @ try_drule rule
                            else [(false, rule)]
                      | _      => [(false, rule)]
                    end
                    handle THM _ => []
                  ) (Attrib.eval_thms ctxt [raw_rule])
              end ) raw_rules
          |> transpose []
     in st
     |> Thm.biresolution NONE false rules 1
     |> Seq.map ( Thm.solve_constraints
               #> Config.get ctxt auto_deconflict_bound ? deconflict_bound_names_thm)
     |> Seq.pull
     |> (fn SOME (st', _) =>
              (* Emit only the newly-opened subgoals (M = new prems from
                 rule), not the whole prems list, so nested RULE
                 applications get a child count aligned with "subgoals
                 this rule opened" — not "all remaining prems on the top
                 HHF".  Mirrors the same fix in `raw_apply` above. *)
              let val n_new = Thm.nprems_of st' - Thm.nprems_of st + 1
                  val new_goals = take n_new (Thm.prems_of st')
               in get_reporter () (Goals new_goals)
                ; (ctxt, HHF (protect_goals st', items) :: SK)
              end
          | NONE => raise OPR_FAIL (PROOF_FAIL, "Fail to apply the rules" ))
     |> maintain
    end
  | RULE' _ _ _ = raise BROKEN_INVARIANT

val RULE = timed_OPR 8 oo RULE'
val RULE_CMD = let open Parse
      in Scan.optional thms1 []
      -- Scan.optional (($$$ "with" || $$$ "WITH") |-- thms1) [] >> uncurry RULE
     end


(** HAVE **)

(*
fun HAVE'' _ _ _ (ctxt, []) = (ctxt, [])
  | HAVE'' AP raw_name expr (ctxt, HHF (G,items) :: S) =
      let val (name, ctxt) = case raw_name of
                SOME (name, raw_attrs) =>
                  ((Binding.name name,
                    raw_attrs |> map ( Attrib.check_src ctxt
                                    #> Attrib.attribute ctxt )), ctxt)
              | NONE =>
                  let val jj_val = get_fact_counter ctxt
                      val b = Binding.name ("fact" ^ string_of_int jj_val)
                      val (_, ctxt') = map_fact_counter (fn n => ((), n + 1)) ctxt
                   in ((b, []), ctxt')
                  end
          val goal_term = Syntax.read_prop ctxt expr
          val goal = Goal.init (Thm.cterm_of ctxt goal_term)
          fun CB ctxt' (st',(*items'*) _,S, _) =
            let val lem = Goal.conclude st'
                       |> singleton (Proof_Context.export ctxt' ctxt)
             in AP (ctxt,name,items,G,S,lem)
            end
          fun PRT _ t = BUNDL (items, [t, print_stack [HHF (G,([],[]))]])
       in (ctxt, HHF (goal, ([],[])) :: ENDBLK T_END :: MAGIC (CB, PRT, NO_PARAM) :: S)
      end
  | HAVE'' _ _ _ _ = raise BROKEN_INVARIANT

val HAVE' = HAVE'' (fn (ctxt,name,items,st,S,lem) =>
  let val lems = elim_conjs ctxt lem
      val ((name,lems), ctxt'') = Proof_Context.note_thms "" (name, [(lems,[])]) ctxt
      val flattened_facts = flatten_facts [(name, map Thm.prop_of lems)]
   in (ctxt'', HHF (st, cat_items ([], flattened_facts) items) :: S)
  end)

val HAVE = OPR oo HAVE'

val HAVE_CMD =
        Scan.option (Parse.name -- Parse.opt_attribs --| \<^keyword>\<open>:\<close>) --
        Parse.term
     >> (fn (name, expr) => HAVE name expr)
*)

fun gen_HAVE' mkG shows (ctxt0, HHF (st,items) :: S) =
      let
          val s01 = mkG ctxt0
          val ctxt01_raw = Proof.context_of s01
          val goal = #goal (Proof.goal s01)
                  |> init_goal ctxt01_raw

          (* Implicitly fix free vars of the goal (body-mode bypass,
             same pattern as SUFFICES'). *)
          val ctxt01 = ctxt01_raw
              |> Variable.set_body false
              |> Proof_Context.augment (Thm.prop_of goal)
              |> Variable.restore_body ctxt01_raw

          val newly_fixed =
            Variable.add_newly_fixed ctxt01 ctxt0 (Thm.prop_of goal) []
          val _ =
            if null newly_fixed then ()
            else get_reporter ()
                   (Newly_Fixed (map (apfst (Variable.revert_fixed ctxt01))
                                     newly_fixed))

          val binds = map (apsnd (map (Attrib.attribute_cmd ctxt0)) o fst) shows
          fun CB ctxt' (st',(*items'*) _,S, _) =
            let val lems = Goal.conclude st'
                        |> finalize_goal ctxt'
                        |> Conjunction.elim_conjunctions
                        |> Proof_Context.export ctxt' ctxt0
                        |> unflat (map snd shows)
                val (lems, ctxt02) = Proof_Context.note_thmss "" (binds ~~ map (fn x => [(x, [])]) lems) ctxt0
                val ctxt03 = Proof_Context.auto_bind_facts (maps (map Thm.prop_of o snd) lems) ctxt02
                val items' = ([], lems |> map (apsnd (map Thm.prop_of)) |> flatten_facts)
                val (itemss, ctxt04) = fold_map extend_calc (maps snd lems) ctxt03
             in get_reporter () (New_Items items')
              ; (ctxt04, HHF (st, cat_items ([], flat itemss) (cat_items items' items)) :: S)
            end

          val thy01 = Proof_Context.theory_of ctxt01
          val preruns = concl_of (Thm.prop_of goal)
                  |> Logic.dest_conjunctions
                  |> filter_out (fn Const(\<^const_name>\<open>Pure.term\<close>, _) $ _ => false
                                  | _ => true)
                  |> map (Skip_Proof.make_thm thy01)
                  |> unflat (map snd shows)
          val (fakes, _) = Proof_Context.note_thmss "" (binds ~~ map (fn x => [(x, [])]) preruns) ctxt0
          val items' = ([], fakes |> map (apsnd (map Thm.prop_of)) |> flatten_facts)

          fun PRT _ t = BUNDL (items, [BLOCK t, print_stack [HHF (st, items')]])
       in (ctxt01, HHF (goal, ([],[])) :: ENDBLK T_END :: MAGIC (CB, PRT, NO_PARAM) :: S)
      end
  | gen_HAVE' _ _ _ = raise BROKEN_INVARIANT

fun gen_HAVE mkspec fixes assumes shows =
  timed_OPR 8 (
     TRANSPARENT_INTRO'
  #> (fn (ctxt, SK) =>
    let val delta = fold (fn ((B,_),_) => fn N =>
                            if Binding.is_empty B then (N+1) else N
                         ) shows 0
        val (i', ctxt') = incr_fact_counter delta ctxt
        val i = Unsynchronized.ref i'
        fun mkB () = let val j = !i
                      in i := j + 1
                       ; Binding.name ("fact" ^ string_of_int j)
                     end
        val shows' = map (fn origin as ((B,atts),props) =>
                            if Binding.is_empty B then ((mkB(),atts),props) else origin ) shows
     in gen_HAVE' (mkspec false "" NONE (K I) Binding.empty_atts []
                  [Element.Fixes fixes, Element.Assumes assumes] (Element.Shows shows) false)
                  shows' (ctxt', SK)
    end ))

val HAVE   = gen_HAVE Specification.schematic_theorem_cmd
val HAVE'' = gen_HAVE Specification.schematic_theorem

val HAVE_CMD =
        Parse_Spec.statement -- Parse_Spec.if_statement -- Parse.for_fixes
     >> (fn ((shows, assumes), fixes) =>
          tolerate_typ (HAVE fixes assumes shows)
                       (fn s => HAVE fixes (remove_typ_ass assumes) (remove_typ_ass shows) s) )

fun atomize_term ctxt =
      Object_Logic.atomize_term ctxt
  #> (fn X => if Term.fastype_of X = \<^Type>\<open>bool\<close>
              then X
              else raise OPR_FAIL (INVALID_OPR, "Fail to atomize the proposition into HOL"))

(** SUFFICES **)

(* Check if a term contains schematic variables *)
fun has_schematic_vars tm =
  let fun check (Var _) = true
        | check (Abs (_, _, body)) = check body
        | check (f $ x) = check f orelse check x
        | check _ = false
   in check tm
  end

(* Apply a "suffices" rule to transform a goal using P --> G *)
fun apply_suffices_rule st impl_lem ctxt =
  let
    (* impl_lem is: ⊢ P --> G *)
    (* We want to apply it backward to st, replacing goal G with P *)

    (* Strategy: Use mp rule in backward direction
       The mp rule is: [| ?P --> ?Q; ?P |] ==> Q
       We instantiate this with our P and G, then resolve with impl_lem
       to get P ==> G, which we apply backward to replace G with P *)

    val prop = Thm.prop_of impl_lem
    val (prop_P, prop_G) = case prop of
        Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ P $ G)
          => (P, G)
      | _ => raise OPR_FAIL (INVALID_OPR, "Expected HOL implication P --> G")

    (* Get the mp theorem: [| ?P --> ?Q; ?P |] ==> ?Q *)
    val mp_thm = @{thm mp}

    (* Extract the Var structure from mp theorem *)
    val mp_prems = Logic.strip_imp_prems (Thm.prop_of mp_thm)
    val prem1_imp = HOLogic.dest_Trueprop (hd mp_prems)
    val (P_term, Q_term) = HOLogic.dest_imp prem1_imp
    val ((P_name, P_idx), P_typ) = Term.dest_Var P_term
    val ((Q_name, Q_idx), Q_typ) = Term.dest_Var Q_term

    (* Instantiate mp_thm with our specific P and G *)
    val inst = Thm.instantiate
                 (TVars.empty,
                  Vars.make [(((P_name, P_idx), P_typ), Thm.cterm_of ctxt prop_P),
                             (((Q_name, Q_idx), Q_typ), Thm.cterm_of ctxt prop_G)])
                 mp_thm

    (* Resolve impl_lem with instantiated mp to get: P ==> G *)
    val resolved = impl_lem RS inst

    (* Apply this backward to replace goal G with P *)
    val result = Thm.biresolution (SOME ctxt) false [(false, resolved)] 1 st
              |> Seq.pull

   in case result of
        SOME (st', _) => protect_goals st'
      | NONE => raise OPR_FAIL (INVALID_OPR,
                  "Failed to apply suffices rule - goal might not match")
  end

fun SUFFICES' intro_bindings prep_prop raw_prop (ctxt0, HHF (st0, items0) :: S) =
  let
    (* Extract the current goal *)
    val goals = goals_of' st0
    val goal_G = case goals of
                   [] => raise OPR_FAIL (INVALID_OPR, "SUFFICES requires at least one goal")
                 | (G :: _) => Logic.strip_assums_concl G

    (* Check for schematic variables in goal *)
    val _ = if has_schematic_vars goal_G
            then raise OPR_FAIL (INVALID_OPR,
                   "SUFFICES does not support goals with schematic variables")
            else ()

    (* Parse the sufficient condition P *)
    val prop_P_raw = prep_prop ctxt0 raw_prop
    val prop_P = case prop_P_raw of
                   Const(\<^const_name>\<open>Trueprop\<close>, _) $ P => P
                 | P => P

    (* Create HOL implication: P --> G (where G is atomized if needed) *)
    val goal_G_atom = case goal_G of
                        Const(\<^const_name>\<open>Trueprop\<close>, _) $ G => G
                      | G => G
    val impl_term = HOLogic.mk_imp (prop_P, goal_G_atom)
                 |> HOLogic.mk_Trueprop

    (* Implicitly fix free vars of P (body-mode bypass, same pattern as gen_HAVE'). *)
    val ctxt_setup = ctxt0
                  |> Variable.set_body false
                  |> Proof_Context.augment impl_term
                  |> Variable.restore_body ctxt0

    val impl_goal = Thm.cterm_of ctxt_setup impl_term
                 |> Goal.init
                 |> init_goal ctxt_setup

    (* Callback when P --> G is proven *)
    fun CB ctxt' (impl_thm, _, SK', _) =
      let
        (* Extract the proven lemma: P --> G *)
        val impl_lem = Goal.conclude impl_thm
                    |> finalize_goal ctxt'
                    |> singleton (Proof_Context.export ctxt' ctxt0)

        (* Apply the implication backward to replace G with P *)
        val new_st = apply_suffices_rule st0 impl_lem ctxt0
        val state_after = (ctxt0, HHF (new_st, items0) :: SK')

      in case intro_bindings of
           NONE => state_after
         | SOME (var_names, prem_names) =>
             #2 (INTRO' SINGLE_GOAL NONE var_names prem_names state_after)
      end

    fun PRT _ t = BUNDL (items0, [BLOCK t, print_stack [HHF (st0, empty_items)]])

    (* Report the new goal P --> G explicitly *)
    val _ = get_reporter () (Goals [impl_term])

  in (ctxt_setup, HHF (impl_goal, ([],[]))
          :: ENDBLK T_END
          :: MAGIC (CB, PRT, NO_PARAM)
          :: S)
  end
  | SUFFICES' _ _ _ _ = raise BROKEN_INVARIANT

fun gen_SUFFICES mk_stmt raw_fixes raw_assumes raw_shows =
  timed_OPR 8 (
     TRANSPARENT_INTRO'
  #> (fn (ctxt0, SK) =>
    let
        val raw_assume_propss = map snd raw_assumes
        val raw_show_propss = map snd raw_shows

        val ({vars, propss, ...}, params_ctxt) =
              mk_stmt raw_fixes (raw_assume_propss @ raw_show_propss) ctxt0

        val fixes = map #2 vars
        val (premss, conclss) = chop (length raw_assumes) propss

        val concl_terms = flat conclss
        val _ = if null concl_terms
                then raise OPR_FAIL (INVALID_OPR, "SUFFICES requires at least one conclusion")
                else ()
        val concl = case concl_terms of
              [t] => t
            | ts => HOLogic.mk_Trueprop (
                      foldr1 HOLogic.mk_conj (map HOLogic.dest_Trueprop ts))

        val closed = Logic.close_prop fixes (flat premss) concl
        val hol_prop = atomize_term params_ctxt closed

        val newly_fixed =
            Variable.add_newly_fixed params_ctxt ctxt0 closed []
        val _ = if null newly_fixed then ()
                else get_reporter ()
                       (Newly_Fixed (map (apfst (Variable.revert_fixed params_ctxt))
                                         newly_fixed))

        val intro_var_names =
            if null raw_fixes then NONE
            else SOME (map (fn (b, _, _) => SOME (Binding.name_of b)) raw_fixes)

        val intro_prem_names =
            let val names = maps (fn ((b, _), props) =>
                  if Binding.is_empty b then replicate (length props) NONE
                  else let val base = Binding.name_of b
                       in replicate (length props) (SOME base)
                       end
                ) raw_assumes
            in if null names then NONE else SOME names
            end

        val intro_bindings =
            if null raw_fixes andalso null raw_assumes then NONE
            else SOME (intro_var_names, intro_prem_names)

        val _ = case intro_bindings of NONE => ()
              | SOME (var_names, prem_names) =>
          let fun count (Const(\<^const_name>\<open>Trueprop\<close>, _) $ t) = count t
                | count (Const(\<^const_name>\<open>HOL.All\<close>, _) $ Abs(_, _, body)) =
                    apfst (fn n => n + 1) (count body)
                | count (Const(\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ body) =
                    apsnd (fn n => n + 1) (count body)
                | count _ = (0, 0)
              val (nq, np) = count hol_prop
              val nv = length (the_default [] var_names)
              val nn = length (the_default [] prem_names)
              val _ = if nv > 0 andalso nq <> nv
                      then raise OPR_FAIL (INVALID_OPR,
                        "SUFFICES: expected " ^ string_of_int nq ^
                        " variable binding(s) but got " ^ string_of_int nv)
                      else ()
              val _ = if nn > 0 andalso np <> nn
                      then raise OPR_FAIL (INVALID_OPR,
                        "SUFFICES: expected " ^ string_of_int np ^
                        " premise binding(s) but got " ^ string_of_int nn)
                      else ()
          in () end

    in SUFFICES' intro_bindings (K I) hol_prop (ctxt0, SK)
    end ))

val SUFFICES   = gen_SUFFICES Proof_Context.read_stmt
val SUFFICES'' = gen_SUFFICES Proof_Context.cert_stmt

val SUFFICES_CMD =
    Parse_Spec.statement -- Parse_Spec.if_statement -- Parse.for_fixes
 >> (fn ((shows, assumes), fixes) =>
      tolerate_typ
        (SUFFICES fixes assumes shows)
        (fn s => SUFFICES fixes (remove_typ_ass assumes)
                   (remove_typ_ass shows) s))

(** INST_VAR **)

fun INST_VAR' prep_term insts (ctxt, HHF (st, items) :: SK) =
  let
    (* Parse all instantiation terms *)
    val insts_terms = map (fn (idx, raw) => (idx, prep_term ctxt raw)) insts

    (* Build the instantiation for Thm.instantiate *)
    (* Each instantiation needs: ((indexname, typ), cterm) *)
    val schematic_vars = Term.add_vars (Thm.prop_of st) []

    (* Create a lookup table for variable types *)
    val var_types = map (fn ((name, idx), typ) => ((name, idx), typ)) schematic_vars
                 |> AList.lookup (op =)

    (* Build the Vars table for instantiation *)
    val inst_pairs = map (fn (idx, t) =>
          case var_types idx of
            SOME typ =>
              let val cterm = Thm.cterm_of ctxt t
               in ((idx, typ), cterm)
              end
          | NONE => raise OPR_FAIL (INVALID_OPR,
                      "Variable " ^ Term.string_of_vname idx ^
                      " not found in goal")
        ) insts_terms

    val inst = (TVars.empty, Vars.make inst_pairs)

    (* Apply the instantiation *)
    val st' = Thm.instantiate inst st

   in (ctxt, HHF (st', items) :: SK)
  end
  | INST_VAR' _ _ _ = raise BROKEN_INVARIANT

fun gen_INST_VAR prep_term insts = timed_OPR 8 (INST_VAR' prep_term insts)

val INST_VAR   = gen_INST_VAR Syntax.read_term
val INST_VAR'' = gen_INST_VAR (K I)

(* Parser for INST_VAR_CMD *)
val INST_VAR_CMD =
  let
    val single_inst = Args.var --| Args.$$$ "=" -- Parse.term
   in Parse.and_list1 single_inst >> INST_VAR
  end

(** SPECIALIZE **)

(* Instantiate universal quantifiers in a rule and discharge its premises left-to-right.
   The result is bound as a local fact in the proof context. *)
fun SPECIALIZE' prep_thms prep_insts opt_name raw_rules raw_insts raw_facts
                (ctxt, HHF (st, items) :: SK) =
  let
    (* 1. Resolve the rule *)
    val rules = prep_thms ctxt raw_rules
    val rule = case rules of [r] => r
              | _ => raise OPR_FAIL (INVALID_OPR,
                      "SPECIALIZE expects exactly one rule, got " ^
                      string_of_int (length rules))

    (* 2. Instantiate universal quantifiers and schematic variables *)
    val insts = prep_insts ctxt raw_insts
    val rule' = Minilang_Aux.inst_universal_quantifiers ctxt insts rule
                handle ERROR msg =>
                  let val rule_name =
                        if Thm.has_name_hint rule
                        then Minilang_Aux.simp_fact_name' (Thm.get_name_hint rule)
                        else "<anonymous>"
                  in raise OPR_FAIL (INVALID_OPR, String.concat [
                       "cannot instantiate rule \<open>", rule_name, "\<close>:\n",
                       msg, "\n",
                       "the rule is:\n  ", Thm.string_of_thm ctxt rule]) end

    (* 3. Discharge premises left-to-right with facts.
       xOF handles both Pure.imp and HOL.implies/HOL.All.
       prove_discharge=true: if OF unification fails, fall back to proving
       the discharge via insert_tac + fast_mepo_tac. *)
    val facts = prep_thms ctxt raw_facts
    val result = if null facts then rule'
                 else Minilang_Aux.xOF true ctxt (map SOME facts) rule'
                      handle THM _ =>
                        raise OPR_FAIL (INVALID_OPR,
                          case Unify_Diagnostic.diagnose_of_failure ctxt rule' facts of
                            SOME msg => msg
                          | NONE => "the given facts mismatch the rule premises")

    (* 4. Generate name if not provided *)
    val (name, ctxt') = case opt_name of
        SOME n => ((Binding.name n, []), ctxt)
      | NONE => let val jj = get_fact_counter ctxt
                    val (_, ctxt') = map_fact_counter (fn n => ((), n + 1)) ctxt
                 in ((Binding.name ("fact" ^ string_of_int jj), []), ctxt') end

    (* 5. Note the result as a local fact *)
    val lems = elim_conjs ctxt' result
    val ((noted_name, noted_lems), ctxt'') =
          Proof_Context.note_thms "" (name, [(lems, [])]) ctxt'
    val flattened = flatten_facts [(noted_name, map Thm.prop_of noted_lems)]
  in
    (ctxt'', HHF (st, cat_items ([], flattened) items) :: SK)
  end
  | SPECIALIZE' _ _ _ _ _ _ _ = raise BROKEN_INVARIANT

fun gen_SPECIALIZE prep_thms prep_insts opt_name raw_rules raw_insts raw_facts =
  timed_OPR 8 (SPECIALIZE' prep_thms prep_insts opt_name raw_rules raw_insts raw_facts)

fun read_inst_terms ctxt raw_insts =
  let val (vns, raws) = ListPair.unzip raw_insts
      val terms = Syntax.read_terms (Proof_Context.set_mode Proof_Context.mode_pattern ctxt) raws
   in vns ~~ terms end

val SPECIALIZE   = gen_SPECIALIZE Attrib.eval_thms read_inst_terms
val SPECIALIZE'' = gen_SPECIALIZE (K I) (K I)

local
  val ident = Parse.token
    (Parse.short_ident || Parse.long_ident || Parse.sym_ident || Parse.term_var ||
      Parse.type_ident || Parse.type_var || Parse.number)
  val var_name_parser =
    (ident >> Token.content_of) :|-- (fn x =>
      if String.isPrefix "?" x then
        case Lexicon.read_variable x of
          SOME xi => Scan.succeed (Minilang_Aux.VN_IndexName xi)
        | NONE => Scan.fail
      else Scan.succeed (Minilang_Aux.VN_Name x))
in
val SPECIALIZE_CMD =
  let open Parse
      val where_clause =
        Scan.optional (($$$ "where" || $$$ "WHERE")
          |-- and_list1 (var_name_parser --| Args.$$$ "=" -- term)) []
      val with_clause =
        Scan.optional (($$$ "with" || $$$ "WITH") |-- thms1) []
   in Scan.option (name --| $$$ ":") -- thms1 -- where_clause -- with_clause
      >> (fn (((opt_name, rules), insts), facts) =>
            SPECIALIZE opt_name rules insts facts)
  end
end

(** CONSIDER **)

(*can be cached*)
fun mk_consider_rule ctxt DNF_SPEC =
  let fun var TS name =
        let val EN = length TS
         in Var((name,0), (map #2 TS) ---> \<^Type>\<open>bool\<close>)
         |> fold (fn (i,_) => fn X => X $ Bound (EN - 1 - i)) TS
        end
      fun mk_conj_clause (ii, (EN,CN)) =
        let val TS = List.tabulate (EN, fn i =>
                      (i, TVar (("'x" ^ string_of_int ii ^ "'" ^ string_of_int i, 0), \<^sort>\<open>type\<close>)))
            val PS = List.tabulate (CN, fn i =>
                      var TS ("P"  ^ string_of_int ii ^ "'" ^ string_of_int i))
         in foldr1 (fn (A,B) => \<^Const>\<open>conj\<close> $ A $ B) PS
         |> fold_rev (fn (i,T) => fn X =>
                      \<^Const>\<open>Ex T\<close> $ Abs ("x" ^ string_of_int ii ^ "'" ^ string_of_int i, T, X)) TS
        end
      fun import_vars ctxt th =
        let val ((_, [th']), ctxt') = ctxt |> Variable.set_body false |> Variable.import true [th];
         in (ctxt', th')
        end
      val C = HOLogic.mk_Trueprop (var [] "C")
   in map_index mk_conj_clause DNF_SPEC
   |> foldr1 (fn (A,B) => \<^Const>\<open>disj\<close> $ A $ B)
   |> (fn X => Logic.mk_implies (HOLogic.mk_Trueprop X, C))
   |> Thm.cterm_of ctxt
   |> Thm.trivial
   |> import_vars ctxt
   |-> (fn ctxt' => fn th => th
   |> Seq.REPEAT (REPEAT_DETERM_SOME (Thm.biresolution NONE true
              [(true, Thms.exE), (true, Thms.conjE), (true, Thms.disjE)]))
   |> Seq.hd
   |> Thm.permute_prems 0 ~1
   |> singleton (Variable.export ctxt' ctxt))
  end

fun CONSIDER'i raw_dnf (ctxt0, HHF (st0, items0) :: S) =
  let fun parse (raw_decls, (raw_fixes, raw_prems, raw_statements)) ctxt =
        let val raw_props = map snd raw_statements
      
            val binders = map fst raw_statements
                       |> map (apsnd (map ( Attrib.check_src ctxt
                                         #> Attrib.attribute ctxt )))

            val (binders, ctxt) = map_fact_counter (fn jj_val =>
                  fold_map (fn (B,AT) => fn N =>
                      if Binding.is_empty B
                      then ((Binding.name ("fact" ^ string_of_int N), AT), N+1)
                      else ((B,AT),N)) binders jj_val
                ) ctxt
      
            val ({vars, propss, binds, result_binds, ...}, params_ctxt) =
                    Proof_Context.read_stmt (raw_decls @ raw_fixes) (raw_prems @ raw_props) ctxt
            val (decls, fixes) = chop (length raw_decls) vars ||> map #2;
            val (premss, conclss) = chop (length raw_prems) propss;

            val (params_ctxt, decls, conclss) =
              if Config.get ctxt0 high_auto_mode
              then let
                   fun ex_var_of (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) ret = ex_var_of X ret
                     | ex_var_of (Const(\<^const_name>\<open>Ex\<close>, _) $ Abs (name,ty,X)) ret
                          = ex_var_of X ((name,ty) :: ret)
                     | ex_var_of _ ret = rev ret
                   val vs = fold (fold ex_var_of) conclss []
                         |> Variable.variant_frees params_ctxt []
                in if null vs
                 then (params_ctxt, decls, conclss)
                 else let
                   val (names, params_ctxt) = Variable.add_fixes (map fst vs) params_ctxt
                   val decls = map2 (fn name => fn (xname, ty) =>
                                 ((Binding.name xname, SOME ty, NoSyn), (xname, Free (name, ty)))
                               ) names vs @ decls
                   val vars = map2 (fn name => fn (_, ty) => Free (name, ty)) names vs
                   fun sub_one (var::vars) (Const(\<^const_name>\<open>Ex\<close>, _) $ Abs (_, _, X)) =
                        sub_one vars (Term.subst_bound (var, X))
                     | sub_one [] (Const(\<^const_name>\<open>Ex\<close>, _) $ _) =
                        error "CONSIDER'i :: Insuffient vars"
                     | sub_one vars ((H as Const(\<^const_name>\<open>Trueprop\<close>, _)) $ X) =
                        let val (vars', X') = sub_one vars X
                         in (vars', H $ X')
                        end
                     | sub_one vars X = (vars, X)
                   fun subs [] [] = []
                     | subs _ [] = error "CONSIDER'i :: more vars"
                     | subs vs (concl :: concls) =
                        let val (vs', concl') = sub_one vs concl
                            val concls' = subs vs' concls
                         in concl' :: concls'
                        end
                in (params_ctxt, decls, burrow (subs vars) conclss)
               end
               end
              else (params_ctxt, decls, conclss)

            val propss' = (map o map) (Logic.close_prop fixes (flat premss)) conclss
                       |> flat
                       |> map (atomize_term ctxt)
            val AS = map (Thm.cterm_of ctxt o HOLogic.mk_Trueprop) propss'
      
            val goal = propss'
                    |> foldr1 (fn (A, B) => \<^Const>\<open>conj\<close> $ A $ B)
                    |> fold_rev (fn (_, t) => fn T =>
                          \<^Const>\<open>Ex \<open>Term.type_of (snd t)\<close>\<close> $ Term.lambda_name t T
                        ) decls
      
            val cparams = map (Thm.cterm_of params_ctxt o #2 o #2) decls
         in ((cparams,
             (length decls, length propss'),
             (decls,
              fixes,
              AS,
              raw_props,
              binds,
              binders),
             (goal,
              result_binds)),
             params_ctxt)
        end

      val (conj_clauses, params_ctxt) = fold_map parse raw_dnf ctxt0
      val rule0 = mk_consider_rule ctxt0 (map #2 conj_clauses)

      val goal0= map (#1 o #4) conj_clauses
              |> foldr1 (fn (A,B) => \<^Const>\<open>disj\<close> $ A $ B)
              |> (fn X => HOLogic.Trueprop $ X)
      (* CONSIDER opens 1 + N subgoals as user-facing children:
         - goal0: the exhaustiveness disjunction (prove this first)
         - N case bodies: prove the original goal under each case's assumption
         Each case body's goal term is the original leading goal of `st0`.
         Emit all N+1 so the Python SubgoalMaker's Goals-based child count
         matches the actual stack structure. *)
      val case_body = fst (Logic.dest_implies (Thm.prop_of st0))
      val _ = get_reporter () (Goals (goal0 :: map (K case_body) conj_clauses))
      val goal = goal0
              |> Thm.cterm_of params_ctxt
              |> Goal.init
              (* |> singleton (Variable.export params_ctxt ctxt0) *)
      val goal_binds = map (#2 o #4) conj_clauses
              |> foldl1 (AList.merge (op =) (op aconv))
      val ctxt_rule = params_ctxt
                   |> fold Variable.bind_term goal_binds

      val subgoals = map (fn (_, _, (decls, fixes, AS, raw_props, _, binders), _) =>
              print_stack [HHF (st0, (  map (apsnd Term.fastype_of o snd) decls
                                      @ map (apsnd Term.fastype_of) fixes,
                                     flatten_facts (map (Binding.name_of o fst) binders ~~
                                        (unflat raw_props (map Thm.term_of AS))) ))] ) conj_clauses
      fun PRT0 sgs _ t = BUNDL (items0, (case conj_clauses of [_] => BLOCK t | _ => t) :: sgs)
      fun CB _ _ [] _  _ = raise BROKEN_INVARIANT
        | CB initial sgs
             ((cparams, _, (decls, fixes, AS, raw_props, binds, binders), _) :: remain_clauses)
             ctxt' (lem, _, S, _) =
            let val rule' = lem
                         |> Goal.conclude
                         |> singleton (Proof_Context.export ctxt' ctxt0)
                         |> initial ? MP ctxt0 rule0
                fun export a b =
                    let val (A,B) = Obtain.obtain_export ctxt0 rule' cparams a b 
                        fun export_thm thm =
                          let val protected = is_protected (Thm.prop_of thm)
                           in thm
                           |> protected? Goal.conclude
                           |> A
                           |> protected? Goal.protect 0
                          end
                     in (export_thm,B)
                    end
                val (lems', ctxt'') = Proof_Context.add_fixes (map #1 decls) ctxt0
                                   |> snd
                                   |> fold (Variable.bind_term o apsnd (Logic.close_term fixes)) binds
                                   |> Assumption.add_assms export AS
                val lems'' = binders ~~ map (map (fn X => ([X],[]))) (unflat raw_props lems')
                val (new_facts, ctxt'3) = Proof_Context.note_thmss "" lems'' ctxt''
                val items_delt = (map (apsnd Term.fastype_of o snd) decls,
                                  new_facts |> map (apsnd (map Thm.prop_of)) |> flatten_facts)
                val items'3 = items_delt
                           |> null remain_clauses ? (fn X => cat_items X items0)
             in get_reporter () (New_Items items_delt)
              ; (ctxt'3, HHF (st0, items'3)
                          :: (case remain_clauses
                                of [] => S
                                 |  _ =>    ENDBLK T_NXT
                                         :: MAGIC (CB false (tl sgs) remain_clauses,
                                                   PRT0 (tl sgs),
                                                   NO_PARAM)
                                         :: S))
            end

   in (ctxt_rule,
          HHF (goal,([],[]))
       :: ENDBLK (case conj_clauses of [_] => T_END | _ => T_NXT)
       :: MAGIC (CB true subgoals conj_clauses, PRT0 subgoals, NO_PARAM) :: S)
  end
  | CONSIDER'i _ _ = raise BROKEN_INVARIANT

fun CONSIDER' raw_dnf = CONSIDER'i raw_dnf o TRANSPARENT_INTRO'

val structured_statement =
  Parse_Spec.statement -- Parse_Spec.if_statement' -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) => (fixes, assumes, shows));

val CONSIDER = timed_OPR 8 o CONSIDER'
fun CONSIDER_CMD toks = (
     Parse.enum1 "|"
        (Scan.optional (Parse.vars --| Parse.where_) []
          -- structured_statement)
     >> (fn x =>
          tolerate_typ (CONSIDER x)
                       (fn s => CONSIDER (map (apsnd (fn (a,b,c) =>
                                  (a,remove_typ_ss b,remove_typ_ass c) )) x) s)
        )) toks

(** STEP, the alternative calculation mechanism **)

fun STEP' prep_term opt_rule raw_term (ctxt, HHF (st, items) :: SK) =
  let val term0 = prep_term ctxt raw_term
      val (opr, term) = case Term.fastype_of term0
                          of \<^Type>\<open>bool\<close> => (case term0 of opr $ _ $ RHS => (SOME opr, RHS)
                                               | _ => (NONE, term0))
                           | _ => (NONE, term0)
      val term = Thm.cterm_of ctxt term
      fun err () = raise OPR_FAIL (INVALID_OPR, "The goal is not about a known transitive operator")
      fun parse_opr (Const(\<^const_name>\<open>Trueprop\<close>, _) $ X) = parse_opr X
        | parse_opr (C $ _ $ _) = C
        | parse_opr _ = err ()
      
     
      val i = Unsynchronized.ref (Thm.maxidx_of st)
      fun mk_i () = (i := !i + 1; !i)
      fun mkV () = TVar (("'a", mk_i()), [])
      val Y' = ("Y", mk_i())
      val (X,Y,Z) = ( Var(("X", mk_i()), mkV ())
                    , Var(Y', mkV ())
                    , Var(("Z", mk_i()), mkV ()) )
      fun erase (Free (N,_)) = Free (N, mkV ())
        | erase (Var  (N,_)) = Var  (N, mkV ())
        | erase (Const(N,_)) = Const(N, mkV ())
        | erase (X $ Y) = erase X $ erase Y
        | erase (Abs (N,_,X)) = Abs (N,  mkV (), erase X)
        | erase X = X
      val const = parse_opr (Thm.major_prem_of st)
               |> erase
      val opr' = case opr of SOME opr => erase opr | _ => const
      val pat = \<^Const>\<open>Pure.imp\<close> $ HOLogic.mk_Trueprop (opr' $ X $ Y)
                                $ (
                \<^Const>\<open>Pure.imp\<close> $ HOLogic.mk_Trueprop (const $ Y $ Z)
                                $ HOLogic.mk_Trueprop (const $ X $ Z) )
      val thy = Proof_Context.theory_of ctxt
      fun can_match tm = can (Pattern.match thy (pat, tm)) (Vartab.empty, Vartab.empty)

      val rules =
          case opt_rule
            of [] =>
             let 
              in Find_Theorems.find_theorems ctxt NONE NONE true [(true, Find_Theorems.Pattern pat)]
              |> snd
              |> filter (can_match o Thm.prop_of o snd)
              |> map_filter (fn (_, th) =>
                    let fun parse (Const(\<^const_name>\<open>Pure.imp\<close>, _)
                              $ (Const(\<^const_name>\<open>Trueprop\<close>, _) $ (_ $ Var (X, _) $ _))
                              $ (Const(\<^const_name>\<open>Trueprop\<close>, _) $ _))
                                  = X
                          | parse (Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ X) = parse X
                          | parse (Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _, X)) = parse X
                          | parse _ = raise Fail ""
                     in try (Drule.infer_instantiate ctxt [(parse (Thm.prop_of th), term)]) th
                    end handle Fail _ => NONE )
             end
             | rule' =>
                Attrib.eval_thms ctxt rule'

      val st's = rules
             |> map_filter (fn th =>
                  Thm.biresolution (SOME ctxt) true [(false, th)] 1 st
                    |> Seq.pull
                    |> Option.map fst)
             |> distinct (Thm.equiv_thm thy)
      val st' = case st's
                  of st' :: _ => protect_goals st'
                   | [] => err ()
   in (Proof_Context.auto_bind_facts [term0] ctxt,
       HHF (st', items) :: SK)
  end
  | STEP' _ _ _ _ = raise BROKEN_INVARIANT

val STEP   = timed_OPR 8 oo STEP' (K I)
val STEP'' = timed_OPR 8 oo STEP' Syntax.read_term
val STEP_CMD = Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.thms1 --| \<^keyword>\<open>)\<close>) []
            -- Parse.term >> uncurry STEP''


(** CHAINING: explicit, on-demand transitive chain construction **)

fun CHAINING_i name_opt thms (ctxt, HHF (st, items) :: SK) =
      let
        val _ = if null thms
                then raise OPR_FAIL (INVALID_OPR,
                       "CHAINING requires at least one fact")
                else ()

        val (name, ctxt0) = case name_opt of
              SOME n => (n, ctxt)
            | NONE =>
                let val jj = get_fact_counter ctxt
                    val (_, ctxt') =
                      map_fact_counter (fn n => ((), n + 1)) ctxt
                 in ("chain" ^ string_of_int jj, ctxt')
                end

        val stat0 = Proof.init ctxt0
        fun step th st =
              st |> Proof.set_facts [th]
                 |> Calculation.also NONE false
                 |> Seq.pull
                 |> (fn SOME (Seq.Result st', _) => st'
                      | SOME (Seq.Error msg, _) =>
                          raise OPR_FAIL (PROOF_FAIL,
                            "CHAINING: cannot chain fact: " ^ msg ())
                      | NONE =>
                          raise OPR_FAIL (PROOF_FAIL,
                            "CHAINING: no transitivity rule matches"))

        val final =
          fold step thms stat0
            |> Calculation.check
            |> (fn SOME [th] => th
                 | _ => raise OPR_FAIL (PROOF_FAIL,
                          "CHAINING: chain did not resolve to a single theorem"))

        val (new_facts, ctxt') =
          Proof_Context.note_thmss ""
            [((Binding.name name, []), [([final], [])])] ctxt0

        val new_items =
          ([], new_facts |> map (apsnd (map Thm.prop_of)) |> flatten_facts)
      in
        (ctxt', HHF (st, cat_items new_items items) :: SK)
      end
  | CHAINING_i _ _ _ = raise BROKEN_INVARIANT

val CHAINING = timed_OPR 8 oo CHAINING_i

fun CHAINING_txt raw_name raw_thms (stack as (ctxt, _)) =
  let val thms = Attrib.eval_thms ctxt raw_thms
   in CHAINING_i (SOME (Binding.name_of raw_name)) thms stack
  end

val CHAINING_CMD =
      Parse.binding --| (Parse.$$$ "with" || Parse.$$$ "WITH") -- Parse.thms1
        >> (fn (b, raw) => timed_OPR 8 (CHAINING_txt b raw))


(** COMPUTE **)

fun simp_conv ctxt ct =
  let val secs = Config.get ctxt Pre_Simproc.simplify_timeout_seconds
  in Timeout.apply (Time.fromSeconds secs) (Simplifier.full_rewrite ctxt) ct
     handle Timeout.TIMEOUT _ => Conv.all_conv ct
          | ERROR _ => Conv.all_conv ct
  end

fun eval_conv ctxt ct =
  case Ground_Eval.eval_ground 60 ctxt ct of
    SOME thm => thm
  | NONE => Conv.all_conv ct

fun COMPUTE' name term (ctxt, HHF (st, items) :: SK) =
  let
    val ct = Thm.cterm_of ctxt term
    val meta_eq = (simp_conv ctxt then_conv eval_conv ctxt) ct
    val _ = if Thm.is_reflexive meta_eq
            then raise OPR_FAIL (PROOF_FAIL,
              "Computation failed: the term may not be executable or timed out.")
            else ()
    val obj_eq = meta_eq RS @{thm meta_eq_to_obj_eq}
    val lems = elim_conjs ctxt obj_eq
    val binding = (Binding.name name, [])
    val ((noted_name, noted_lems), ctxt') =
          Proof_Context.note_thms "" (binding, [(lems, [])]) ctxt
    val flattened = flatten_facts [(noted_name, map Thm.prop_of noted_lems)]
  in (ctxt', HHF (st, cat_items ([], flattened) items) :: SK)
  end
  | COMPUTE' _ _ _ = raise BROKEN_INVARIANT

val COMPUTE = fn name => fn term => timed_OPR 95 (COMPUTE' name term)


(** HAMMER **)

fun conclude_SK (ctxt, HHF (st, itms) :: S) = (ctxt, HHF (conclude_goal st, itms) :: S)
  | conclude_SK _ = raise BROKEN_INVARIANT

exception SH_PRF of string
exception REPLACE_CMD of string * string

val enable_cache_by_step = Config.declare_bool ("enable_cache_by_step", \<^here>) (K true)
val mini_use_improved_SH = Config.declare_bool ("mini_use_improved_SH", \<^here>) (K true)

fun default_prover timeout_opt override ctxt =
  let val improved_SH = Config.get ctxt mini_use_improved_SH
      val override' = if improved_SH then override
                      else Sledgehammer_Fact.no_fact_override
  in fn id => Phi_Sledgehammer_Solver.auto improved_SH override' id timeout_opt
  end

fun HAMMER_i (prover : string option -> Proof.context -> thm -> string * thm)
             step_id (ctxt, HHF (s,facts) :: S) =
  let val (_, _, ID_BASE) = IPS_Data.get ctxt
      val ID = ID_BASE ^ "/" ^ step_id
      val ID' = if Config.get ctxt enable_cache_by_step then SOME ID else NONE
      val s = Pre_Simproc.pre_simproc_on_concl ctxt s
      val (prf, s') = prover ID' ctxt s
                      handle ERROR E => raise OPR_FAIL (PROOF_FAIL, E)
   in get_reporter () (Internal (SH_PRF prf))
    ; (ctxt, HHF (s', facts) :: S)
   |> maintain
  end
  | HAMMER_i _ _ _ = raise BROKEN_INVARIANT

fun HAMMER prover = OPR_ID (HAMMER_i prover o string_of_int)
val HAMMER_CMD = orverride_parser >> (fn ovr =>
  OPR_ID (fn i => fn (stack as (ctxt, _)) =>
    HAMMER_i (default_prover NONE ovr ctxt) (string_of_int i) stack))

(** END / NEXT **)

fun chk_block_end (stack as (ctxt, _)) =
      if Config.get ctxt strict_end andalso not (stack_top_finished stack)
      then raise OPR_FAIL (PROOF_FAIL,
              "Cannot close the proof block because the goal is unsolved yet")
      else ()
fun chk_block_next_or_end (stack as (ctxt, _)) =
      if Config.get ctxt strict_end andalso not (stack_top_no_subgoal stack)
      then raise OPR_FAIL (PROOF_FAIL,
              "Cannot close the proof block because the goal is unsolved yet")
      else ()
fun chk_block_next (stack as (ctxt, _)) =
      if Config.get ctxt strict_end andalso
         not (stack_top_no_subgoal stack andalso not (stack_top_finished stack))
      then raise OPR_FAIL (PROOF_FAIL,
              "Cannot close the proof block because the goal is unsolved yet")
      else ()

(* Generalized END: apply `F` to close a single subgoal in the current
   HHF, then pop the enclosing ENDBLK. When `end_all = true`, keep
   applying `F` until the HHF is empty, and when the popped ENDBLK is
   T_NXT, pop sibling frames until the enclosing T_END is reached. F
   receives a per-iteration index so it can generate distinct Sledge-
   hammer cache keys across loop iterations. *)
fun gen_END end_all (F : int -> stack -> stack) stack =
  let
    fun exhaust i st =
      let val (ctxt, SK) = conclude_SK (F i st)
      in case SK of
           HHF (s', _) :: _ =>
             if no_goal' s' then (i+1, (ctxt, SK))
             else if end_all then exhaust (i+1) (ctxt, SK)
             else (i+1, (ctxt, SK))
         | _ => raise BROKEN_INVARIANT
      end
    val (next_i, (ctxt, SK'1)) = exhaust 0 stack
    val st' = case SK'1 of HHF (st', _) :: _ => st'
                         | _ => raise BROKEN_INVARIANT
  in
    if no_goal' st'
    then case SK'1
      of HHF s :: ENDBLK T_END :: SK' =>
          ( get_reporter () (Internal (REPLACE_CMD ("END", "END")))
          ; maintain (ctxt, HHF s :: SK') |> report_goal )
       | HHF s :: ENDBLK T_NXT :: SK' =>
          if end_all
          then ( get_reporter () (Internal (REPLACE_CMD ("NEXT", "NEXT")))
               ; let val popped = case SK' of MAGIC _ :: rest => rest
                                            | _ => SK'
                     fun F' i = F (i + next_i)
                 in gen_END end_all F' (maintain (ctxt, HHF s :: popped)) end )
          else raise OPR_FAIL (INVALID_OPR,
            "This block should be closed by the NEXT command.")
       | _ => raise BROKEN_INVARIANT
    else raise OPR_FAIL (INVALID_OPR,
      "This block should be closed by the NEXT command.")
  end

(* Generalized NEXT (counterpart to gen_END): apply `F` to close a
   single subgoal in the current HHF. If the HHF still has remaining
   subgoals, return the state with one fewer goal. If the HHF becomes
   empty, pop the enclosing ENDBLK T_NXT and rebuild the MAGIC
   continuation. If the popped ENDBLK is T_END, error (the caller
   said NEXT, not END) — the `on_end` handler allows the caller to
   substitute a recovery behavior (e.g. RELAXED mode's "return the
   unchanged origin state"). *)
fun gen_NXT' param (F : stack -> stack) on_end stack =
  let val (ctxt, SK'1) = conclude_SK (F stack)
      val st' = case SK'1 of HHF (st', _) :: _ => st'
                           | _ => raise BROKEN_INVARIANT
  in
    if no_goal' st'
    then case SK'1
      of HHF s :: ENDBLK T_NXT :: SK' =>
          ( get_reporter () (Internal (REPLACE_CMD ("NEXT", "NEXT")))
          ; case SK' of
              MAGIC (CB, PRT, _) :: SK'' =>
                maintain (ctxt, HHF s :: MAGIC (CB, PRT, param) :: SK'')
                  |> report_goal
            | _ => maintain (ctxt, HHF s :: SK') |> report_goal )
       | HHF _ :: ENDBLK T_END :: _ => on_end ()
       | _ => raise BROKEN_INVARIANT
    else report_goal (ctxt, SK'1)
  end

(* END' and NXT' are now thin wrappers that parameterize the generalized
   helpers with the Sledgehammer-backed closing tactic. *)
fun END' param SH_override ID (stack as (_, HHF _ :: _)) =
  let val _ = chk_block_end stack
      val ctxt0 = #1 stack
      val end_all = not (Config.get ctxt0 strict_end) andalso
                    member (op =) ["COMPLETE_NEXT", "RELAXED"]
                                  (Config.get ctxt0 working_mode)
      val prover = default_prover NONE SH_override ctxt0
      fun F i =
        let val id_base =
              if i = 0 then string_of_int ID
              else string_of_int ID ^ "+" ^ string_of_int i
        in HAMMER_i prover id_base end
  in gen_END end_all F stack end
  | END' _ _ _ _ = raise BROKEN_INVARIANT

fun NXT' param SH_override ID (origin as stack as (_, HHF _ :: _)) =
  let val _ = chk_block_next stack
      val ctxt0 = #1 stack
      val prover = default_prover NONE SH_override ctxt0
      val F = HAMMER_i prover (string_of_int ID)
      fun on_end () =
        case Config.get ctxt0 working_mode of
            "RELAXED" => origin
          | _ => raise OPR_FAIL (INVALID_OPR,
                   "This block should be closed by the END command.")
  in gen_NXT' param F on_end stack end
  | NXT' _ _ _ _ = raise BROKEN_INVARIANT

(* The polymorphic "auto-advance" helper used by the legacy SORRY
   command, which picks between NEXT and END based on the ENDBLK type. *)
fun gen_END_or_NXT' param F stack =
  let val (ctxt, SK'1) = conclude_SK (F stack)
      val st' = case SK'1 of HHF (st', _) :: _ => st'
                           | _ => raise BROKEN_INVARIANT
   in if no_goal' st'
    then case SK'1
      of HHF s :: ENDBLK T' :: SK' =>
          let val opr = case T' of T_NXT => "NEXT" | T_END => "END"
           in get_reporter () (Internal (REPLACE_CMD (opr, opr)))
            ; case (T', SK')
                of (T_NXT, MAGIC (CB, PRT, _) :: SK'') =>
                        maintain (ctxt, HHF s :: MAGIC (CB, PRT, param) :: SK'')
                     |> report_goal
                 | _ => maintain (ctxt, HHF s :: SK')
                     |> report_goal
          end
       | _ => raise BROKEN_INVARIANT
    else report_goal (ctxt, SK'1)
  end

fun END_or_NXT' param SH_override ID stack =
  let val ID_BASE = string_of_int ID
   in chk_block_next_or_end stack
    ; gen_END_or_NXT' param (HAMMER_i (default_prover NONE SH_override (#1 stack)) ID_BASE) stack
  end

fun END SH_override = OPR_ID (END' NO_PARAM SH_override)
fun NXT param SH_override = OPR_ID (NXT' (CASE_NAME param) SH_override)
fun END_or_NXT param SH_override = OPR_ID (END_or_NXT' (CASE_NAME param) SH_override)
val END_CMD  = orverride_parser >> END
val NXT_CMD  = (fn toks => (OPT_VARS -- orverride_parser >> uncurry NXT ) toks)

fun type_of_end' [] = NONE
  | type_of_end' (ENDBLK typ :: _) = SOME typ
  | type_of_end' (HHF _ :: L) = type_of_end' L
  | type_of_end' (MAGIC _ :: L) = type_of_end' L

val type_of_end = type_of_end' o #2 o #1

(** SORRY **)

fun SORRY_i (ctxt, HHF (s,facts) :: S) =
    let val s' = rule_by_tactic ctxt (Skip_Proof.cheat_tac ctxt 1) s
     in (ctxt, HHF (s', facts) :: S)
     |> maintain
    end
  | SORRY_i _ = raise BROKEN_INVARIANT

fun END_or_NXT'_by_SORRY param = gen_END_or_NXT' param SORRY_i
fun END_or_NXT_by_SORRY param = OPR (END_or_NXT'_by_SORRY (CASE_NAME param))
val END_or_NXT_by_SORRY_CMD = OPT_VARS >> (fn x => END_or_NXT_by_SORRY x)

(* Explicit sorry variants: SORRY_NEXT advances to the next subgoal
   (errors on T_END), SORRY_END_ALL cheats every remaining subgoal and
   closes the enclosing block (handling multi-residual blocks like
   `Define`'s deferred pat-completeness / termination frame). *)
fun SORRY_NEXT (param : opt_var_names) : operation =
  let fun on_end () =
        raise OPR_FAIL (INVALID_OPR,
          "SORRY_NEXT closed the last goal of an END block. " ^
          "Use SORRY_END_ALL to close the entire block.")
  in OPR (gen_NXT' (CASE_NAME param) SORRY_i on_end) end
val SORRY_NEXT_CMD : command = OPT_VARS >> SORRY_NEXT

fun SORRY_END_ALL (_ : opt_var_names) : operation =
  OPR (gen_END true (fn _ => SORRY_i))
val SORRY_END_ALL_CMD : command = OPT_VARS >> SORRY_END_ALL

(* SORRY_ONLY: cheat one subgoal, stay in place — no NEXT / END.
   Analogous to HAMMER but using cheat_tac instead of a prover. *)
val SORRY_ONLY : operation = OPR SORRY_i
val SORRY_ONLY_CMD : command = Scan.succeed SORRY_ONLY

(** LET **)

local

fun gen_bind prep_terms raw_binds ctxt =
    let
      fun prep_bind (raw_pats, t) ctxt1 =
        let
          val T = Term.fastype_of t;
          val ctxt2 = Variable.declare_term t ctxt1;
          val pats = prep_terms (Proof_Context.set_mode Proof_Context.mode_pattern ctxt2) T raw_pats;
          val binds = Proof_Context.simult_matches ctxt2 (t, pats);
        in (binds, ctxt2) end;

      val ts = prep_terms ctxt dummyT (map snd raw_binds);
      val (binds, ctxt') = apfst flat (fold_map prep_bind (map fst raw_binds ~~ ts) ctxt);
      val binds' = map #1 binds ~~ Variable.exportT_terms ctxt' ctxt (map #2 binds);

      val ctxt'' =
        ctxt
        |> fold Variable.declare_term (map #2 binds')
        |> fold Proof_Context.bind_term binds';
      val _ = Variable.warn_extra_tfrees ctxt ctxt'';
    in ctxt'' end

fun read_terms ctxt T =
  map (Syntax.parse_term ctxt #> Type.constraint T) #> Syntax.check_terms ctxt;

in

fun LET' prep_terms raw_binds (ctxt, S) =
      (gen_bind prep_terms raw_binds ctxt, S)

val LET = timed_OPR 3 o LET' (fn ctxt => fn _ => map (Proof_Context.cert_term ctxt))
val LET'' = timed_OPR 3 o LET' read_terms
val LET_CMD =
  (Parse.and_list1 (Parse.and_list1 Parse.term -- (\<^keyword>\<open>=\<close> |-- Parse.term))
    >> (timed_OPR 3 o LET' read_terms))


end

(** CHOOSE -- Instantiate Existential Quantification **)

fun CHOOSE' prep_terms raw_terms (ctxt, HHF (st, items) :: SK) =
  let val terms = prep_terms ctxt raw_terms

      fun rule_of st =
          case Thm.major_prem_of st
            of Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Ex\<close>, _) $ _) => Thms.exI
             | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Ex1\<close>, _) $ _) => Thms.ex1I
             | Const(\<^const_name>\<open>Trueprop\<close>, _) $ (Const(\<^const_name>\<open>Set.Bex\<close>, _) $ _) =>
                Proof_Context.get_thm ctxt "Set.bexI"
             | _ => raise OPR_FAIL (INVALID_OPR, "The leading goal is not about existential quantification")

      val st' = fold (fn term => fn st =>
            let val rule = rule_of st
                        |> Drule.infer_instantiate ctxt [(("x",0), Thm.cterm_of ctxt term)]
             in rule RS st
            end ) terms st
   in report_goal (ctxt, HHF (st', items) :: SK)
  end
  | CHOOSE' _ _ _ = raise BROKEN_INVARIANT

fun read_term ctxt (raw_term, vs) =
  let val (_, ctxt') = Proof_Context.add_fixes_cmd vs ctxt
      val term = Syntax.read_term ctxt' raw_term
   in singleton (Variable.export_terms ctxt' ctxt) term
  end

val CHOOSE = timed_OPR 50000 o CHOOSE' (K I)
val CHOOSE'' = timed_OPR 50000 o CHOOSE' (map o read_term)
val CHOOSE_CMD = Parse.and_list (Scan.repeat1 (Parse.term -- Scan.optional (VARS_KWD |-- Parse.vars) [])) >> (CHOOSE'' o flat)

(** PRINT **)
fun fixes_is_outdated ctxt var_name =
  Name.is_skolem var_name andalso Variable.revert_fixed ctxt var_name = var_name

fun contains_outdated_fixes ctxt term =
  let val vars = Term.add_free_names term []
   in exists (fixes_is_outdated ctxt) vars
  end

(*
fun ap2_3 f (a,b,c) = (a, f b, c)

fun pretty_top_state ctxt tree =
  let open Pretty
      val atom_goals = Config.get ctxt atomize_goals
      val prt_typ = Syntax.pretty_typ ctxt
      val prt_term= Syntax.pretty_term ctxt o (atom_goals ? Object_Logic.atomize_term ctxt)
      fun prt_bundle (vars, facts, term) =
        let val prems = Logic.strip_imp_prems term
            val name = str o simp_fact_name'
            val tails =
                 (if null vars   then [] else [keyword1 "fixed variables"])
                @ map (fn (N,T) => item [str N, brk 1, str "::", brk 1, prt_typ  T]) vars
                @ (if null facts then [] else [keyword1 "contextual facts"])
                @ map (fn (N,[])  => item [name N, brk 1, str ":", brk 1, str "<empty>"]
                        | (N,[T]) => item [name N, brk 1, str ":", brk 1, prt_term T]
                        | (N,TS)  => item [name N, brk 1, str ":", brk 1, chunks (map prt_term TS)]
                      ) facts
         in case prems
         of [] => str "All goals are proven!"
          | [goal] => chunks ( block [keyword1 "goal: ", prt_term goal] :: tails)
          | _  => chunks (
              keyword1 "goals: " ::
              map (fn X => item [prt_term X]) prems
              @ tails)
        end
   in collect_context tree
   |> ap2_3 (map (apsnd (filter_out (contains_outdated_fixes ctxt)))
          #> filter_out (null o snd))
   |> prt_bundle
  end
*)

fun pretty_tree0 _ (BUNDL (_,[])) =
      Pretty.keyword1 "All goals are solved!"
  | pretty_tree0 ctxt tree =
  let open Pretty
      val prt_typ  = Syntax.pretty_typ ctxt
      val prt_term = Syntax.pretty_term ctxt
      val prt_prop =
        if Config.get ctxt transparent_intro
        then strip_prems_universal_vars ctxt
        else fn tm => (ctxt, ([],[]), tm)

      val name = str o simp_fact_name'
      fun pretty_items (vars0, facts0) =
        let val facts = filter_out (contains_outdated_fixes ctxt o snd) facts0
            val vars  = filter_out (fixes_is_outdated ctxt o fst) vars0
         in (if null vars  then [] else [keyword1 "variables"])
          @ map (fn (N,T)   => item [str N, brk 1, str "::", brk 1, prt_typ  T]) vars
          @ (if null facts then [] else [keyword1 "facts"])
          @ map (fn (N,T) => item [name N, brk 1, str ":", brk 1, prt_term T]) facts
        end
      fun pretty prefix (PROP (items, term)) =
          let val (ctxt, items', term) = prt_prop term
              val items = cat_items items' items
           in if items = empty_items andalso null prefix
              then Syntax.pretty_term ctxt term
              else chunks ( keyword1 (String.concat prefix ^ "goal")
                         :: item [Syntax.pretty_term ctxt term]
                         :: pretty_items items )
          end
        | pretty prefix (BUNDL (items, children)) =
              chunks ( keyword1 (String.concat prefix ^ 
                                (case children
                                   of [_] => "goal"
                                    | [ ] => "no goal"
                                    | _ => string_of_int (length children) ^ " subgoals"))
                    :: map (item o single o pretty []) children
                     @ pretty_items items )
        | pretty prefix (BLOCK tree) = pretty ("block of " :: prefix) tree
   in pretty [] (BLOCK tree)
  end

fun pretty_tree ctxt tree = tree
      |> (Config.get ctxt atomize_goals_in_printing orelse Config.get ctxt transparent_intro) ? atomize_tree ctxt
      |> pretty_tree0 ctxt

(* fun pretty_tree (POPL ) *)

fun PRINT (state as ((ctxt,SK), _, ID)) =
  let open Pretty
   in Pretty.writeln (chunks [
        block [keyword1 "proof state after step ", str (string_of_int ID)],
        pretty_tree ctxt (print_stack SK)
      ])
    ; state
  end
val PRINT_CMD = Scan.succeed PRINT

(** NOTATION **)

local

fun read_arg (c, mx) ctxt =
  (case Proof_Context.read_const {proper = false, strict = false} ctxt c of
    Free (x, _) =>
      let
        val ctxt' =
          ctxt |> is_none (Variable.default_type ctxt x) ?
            Variable.declare_constraints (Free (x, Mixfix.default_constraint mx));
        val t = Free (#1 (Proof_Context.inferred_param x ctxt'));
      in ((t, mx), ctxt') end
  | t => ((t, mx), ctxt));

in

fun WRITE' prep_arg mode args (ctxt, SK) =
  (Proof_Context.notation true mode (fst (fold_map prep_arg args ctxt)) ctxt, SK)

val NOTATION   = timed_OPR 3 oo WRITE' pair
val NOTATION'' = timed_OPR 3 oo WRITE' read_arg
val NOTATION_CMD = Parse.syntax_mode -- Parse.and_list1 (Parse.const -- Parse.mixfix)
             >> (fn (mode, args) => timed_OPR 3 (WRITE' read_arg mode args))

end

(** OPEN_MODULE **)

local

fun abs_def_rule eqns ctxt =
  (map (Local_Defs.abs_def_rule ctxt) (maps snd eqns), ctxt);

fun note_eqns_register note add_registration
    deps eqnss witss def_eqns thms export export' ctxt =
  let
    val factss = thms
      |> unflat ((map o map) #1 eqnss)
      |> map2 (map2 (fn b => fn eq =>
          (b, [([Morphism.thm export (Thm.transfer' ctxt eq)], [])]))) ((map o map) #1 eqnss);
    val (eqnss', ctxt') =
      fold_map (fn facts => note Thm.theoremK facts #-> abs_def_rule) factss ctxt;
    val defs = (Binding.empty_atts, [(map (Morphism.thm (export' $> export)) def_eqns, [])]);
    val (eqns', ctxt'') = ctxt' |> note Thm.theoremK [defs] |-> abs_def_rule;
    val transform_witness = Element.transform_witness (Morphism.set_trim_context' ctxt' export');
    val deps' =
      (deps ~~ witss) |> map (fn ((dep, morph), wits) =>
        (dep, morph $> Element.satisfy_morphism (map transform_witness wits)));
    fun register (dep, eqns) ctxt =
      ctxt |> add_registration
        {inst = dep,
          mixin = Option.map (rpair true) (Element.eq_morphism ctxt (eqns @ eqns')),
          export = export};
  in ctxt'' |> fold register (deps' ~~ eqnss') end;

in

fun generic_interpretation prep_interpretation setup_proof note add_registration
    expression raw_defs initial_ctxt =
  let
    val (((propss, eq_propss, deps, eqnss, export, export'), def_eqns), goal_ctxt) =
      prep_interpretation expression raw_defs initial_ctxt;
    fun after_qed witss eqns =
      note_eqns_register note add_registration deps eqnss witss def_eqns eqns export export';
  in setup_proof after_qed propss (flat eq_propss) goal_ctxt end;

end

local

fun augment_with_def prep_term ((name, atts), ((b, mx), raw_rhs)) lthy =
  let
    val rhs = prep_term lthy raw_rhs;
    val lthy' = Variable.declare_term rhs lthy;
    val ((_, (_, def)), lthy'') =
      Local_Theory.define ((b, mx), ((Thm.def_binding_optional b name, atts), rhs)) lthy';
  in (Thm.symmetric def, lthy'') end;

fun augment_with_defs _ [] _ = pair []
      (*quasi-inhomogeneous type: definitions demand local theory rather than bare proof context*)
  | augment_with_defs prep_term raw_defs deps =
      Local_Theory.begin_nested
      #> snd
      #> fold Locale.activate_declarations deps
      #> fold_map (augment_with_def prep_term) raw_defs
      #> Local_Theory.end_nested_result Morphism.fact;

fun prep_interpretation prep_expr prep_term
  expression raw_defs initial_ctxt =
  let
    val ((propss, eq_propss, deps, eqnss, export), expr_ctxt) = prep_expr expression initial_ctxt;
    val (def_eqns, def_ctxt) =
      augment_with_defs prep_term raw_defs deps expr_ctxt;
    val export' = Proof_Context.export_morphism def_ctxt expr_ctxt;
  in (((propss, eq_propss, deps, eqnss, export, export'), def_eqns), def_ctxt) end;

in

fun cert_interpretation expression =
  prep_interpretation Expression.cert_goal_expression Syntax.check_term expression;

fun read_interpretation expression =
  prep_interpretation Expression.read_goal_expression Syntax.read_term expression;

end;

val add_registration = Context.proof_map o Locale.add_registration

fun notes_kind kind facts ctxt =
  let val facts' = map ( apfst (apsnd (map (Attrib.attribute ctxt)))
                      #> apsnd (map (apsnd (map (Attrib.attribute ctxt)))) ) facts
   in Proof_Context.note_thmss kind facts' ctxt
  end

fun interpretation expression =
  generic_interpretation cert_interpretation Element.witness_proof_eqs
    notes_kind add_registration expression []

fun interpretation_cmd expression =
  generic_interpretation read_interpretation Element.witness_proof_eqs
    notes_kind add_registration expression [];


fun OPEN_MODULE' interp expr (lthy, HHF (st, items) :: SK) =
  let val _ = Local_Theory.assert lthy
      val ps = interp expr lthy
      val ctxtp = Proof.context_of ps
      
      fun PRT _ t = BUNDL (items, [t, print_stack [HHF (st, empty_items)]])
      fun CB ctxt' (raw_st', _, SK', _) =
        let val st' = singleton (Proof_Context.export ctxt' ctxtp) raw_st'
            val ctxt'' = Proof.refine_primitive (K (K st')) ps
                      |> Proof.global_done_proof

            val facts = Proof_Context.facts_of ctxt'';
            val local_facts =
              Facts.dest_static false [Proof_Context.facts_of lthy] facts
                |> map (apsnd (map Thm.prop_of))
                |> flatten_facts
            val local_facts = if length local_facts > 16 then [] else local_facts
                  (*Trim off facts if too many*)
            val items' = ([],local_facts)
         in get_reporter () (New_Items items')
          ; (ctxt'',
             HHF (st, cat_items items' items) :: SK')
        end

   in (ctxtp,
       HHF (#goal (Proof.raw_goal ps), empty_items)
       :: ENDBLK T_END
       :: MAGIC (CB, PRT, NO_PARAM)
       :: SK)
   |> report_goal
  end
  | OPEN_MODULE' _ _ _ = raise BROKEN_INVARIANT

val OPEN_MODULE   = timed_OPR 60 o OPEN_MODULE' interpretation
val OPEN_MODULE'' = timed_OPR 60 o OPEN_MODULE' interpretation_cmd
val OPEN_MODULE_CMD = Parse.!!! Parse_Spec.locale_expression
                  >> (timed_OPR 60 o OPEN_MODULE' interpretation_cmd)

(** LOCAL DEFINITION **)

(*TODO: items*)
fun DEFINE' define (ctxt, SK) =
  (Proof.init ctxt
    |> define
    |> Proof.context_of,
   SK)

fun DEFINE   names exprs fixes = timed_OPR 5 (DEFINE' (Proof.define names fixes exprs))
fun DEFINE'' names exprs fixes = timed_OPR 5 (DEFINE' (Proof.define_cmd names fixes exprs))
val DEFINE_CMD = (Parse.vars --| Parse.where_) -- Parse_Spec.statement -- Parse.for_fixes
              >> (fn ((a,b),c) => timed_OPR 5 (DEFINE' (Proof.define_cmd a c b)))


(** RECURSIVE FUNCTION DEFINITION **)

(* Recursively decompose a possibly-quantified, possibly-conditional
   equation. Handles both Pure and HOL connectives in any nesting:
     Pure.all / HOL.All     — quantifiers (stripped)
     Pure.imp / HOL.implies — premises (stripped, flagged)
     Trueprop               — HOL embedding (stripped)
     Pure.eq / HOL.eq       — the equation itself
   Returns SOME ((head, args), rhs, has_prems) or NONE. *)
fun decompose_equation t =
  (case t of
    Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs (_, _, body) =>
      decompose_equation body
  | Const (\<^const_name>\<open>HOL.All\<close>, _) $ Abs (_, _, body) =>
      decompose_equation body
  | Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ concl =>
      decompose_equation concl
      |> Option.map (fn (eq, _) => (eq, true))
  | Const (\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ concl =>
      decompose_equation concl
      |> Option.map (fn (eq, _) => (eq, true))
  | Const (\<^const_name>\<open>HOL.Trueprop\<close>, _) $ inner =>
      decompose_equation inner
  | Const (\<^const_name>\<open>HOL.eq\<close>, _) $ lhs $ rhs =>
      SOME ((strip_comb lhs, rhs), false)
  | Const (\<^const_name>\<open>Pure.eq\<close>, _) $ lhs $ rhs =>
      SOME ((strip_comb lhs, rhs), false)
  | _ => NONE)

(* Check if a parsed equation is compatible with definition:
   head is Free, no premises, simple variable args, non-recursive *)
fun can_use_definition fnames eq =
  (case decompose_equation eq of
    SOME (((Free _, args), rhs), has_prems) =>
      not has_prems
      andalso forall (fn Bound _ => true | Free _ => true | _ => false) args
      andalso not (Term.exists_subterm
        (fn Free (n, _) => member (op =) fnames n | _ => false) rhs)
  | _ => false)

(* Decision: can we use definition or do we need fun?
   Single equation + definition-compatible => true *)
fun can_use_definition_cmd fixes specs ctxt =
  length specs = 1 andalso
  \<^try>\<open>
    let
      val ctxt0 = Variable.set_body false ctxt
      val ((params, named_specs), _) =
        Specification.read_multi_specs fixes specs ctxt0
      val fnames = map (Binding.name_of o fst o fst) params
    in forall (fn (_, eq) => can_use_definition fnames eq) named_specs end
  catch exn => false\<close>

(* ====== FUN: extended pipeline with metric + deferred proof blocks ====== *)

(* Per-phase automatic-tactic timeouts, in seconds. *)
val pat_escalate_timeout =
  Attrib.setup_config_int \<^binding>\<open>fun_pat_escalate_timeout\<close> (K 30)
val term_escalate_timeout =
  Attrib.setup_config_int \<^binding>\<open>fun_term_escalate_timeout\<close> (K 30)

(* Debug only — INTERNAL, not exposed as an attribute. When set,
   force the automatic default termination prover to always report
   DefaultFailed. Affects ONLY the termination phase; pat-completeness
   escalation runs normally regardless of this flag. Used to exercise
   the BY_METRIC code path in tests without needing a function whose
   termination is genuinely hard to automate. Set from ML with e.g.
     setup \<open>Config.put_global Minilang.fun_fake_automatic_failure true\<close> *)
val fun_fake_automatic_failure =
  Config.declare_bool ("Minilang.fun_fake_automatic_failure", \<^here>) (K false)

(* Debug only — INTERNAL, not exposed as an attribute. When set,
   force the pattern-completeness escalation ladder to skip all
   automatic tactic levels and return the untouched goal, leaving
   residual subgoals. Combined with FUN'' open_on_fail = true, this
   pushes the pat-completeness goal onto the minilang stack for
   interactive discharge — useful for testing the Agent interface's
   deferred-pat-completeness code path without needing a function
   whose pat-completeness is genuinely hard to automate. Set from ML
   with e.g.
     setup \<open>Config.put_global Minilang.fun_fake_pat_completeness_failure true\<close> *)
val fun_fake_pat_completeness_failure =
  Config.declare_bool
    ("Minilang.fun_fake_pat_completeness_failure", \<^here>) (K false)

(* Run [tac st] under a timeout. Returns SOME (result state) if the
   tactic produced a state within the timeout; NONE on timeout or if
   the tactic itself fails (via an exception or empty sequence). *)
fun run_with_timeout secs tac st =
  \<^try>\<open>
    (case Timeout.apply (Time.fromSeconds secs)
                       (fn () => SINGLE tac st) () of
        SOME st' => SOME st'
      | NONE => NONE)
    catch _ => NONE\<close>

(* Escalation ladder for pattern-completeness. Tries
     1. pat_completeness; auto
     2. pat_completeness alone
     3. untouched goal
   Always returns a goal state — it may still have open subgoals if
   all three steps leave residuals. Timeout failures drop us to the
   next level. *)
fun escalate_pat ctxt pat_goal_state =
    if Config.get ctxt fun_fake_pat_completeness_failure
    then pat_goal_state       (* debug-only shortcut *)
    else
      let val T = Config.get ctxt pat_escalate_timeout
          val tac1 = Pat_Completeness.pat_completeness_tac ctxt 1 THEN auto_tac ctxt
          val tac2 = Pat_Completeness.pat_completeness_tac ctxt 1
      in
        (case run_with_timeout T tac1 pat_goal_state of
           SOME st => st                           (* Level 1: simplified by (pat_completeness; auto) *)
         | NONE =>
             (case run_with_timeout T tac2 pat_goal_state of
                SOME st => st                      (* Level 2: simplified by pat_completeness alone *)
              | NONE => pat_goal_state))           (* Level 3: untouched *)
      end

(* Wrap a non-empty list of measure-function strings as a single
   well-founded relation. Each metric string is parsed individually
   via Syntax.parse_term (which preserves YXML position markup from
   Parse.embedded_inner_syntax). The wrapper constant is built at the
   term level and the whole thing is type-checked in one call to
   Syntax.check_term.
     []              -> NONE (caller decides)
     [f]             -> SOME (Wellfounded.measure f)
     [f1, f2, ...]   -> SOME (List.measures [f1, f2, ...]) *)
fun wrap_measures _ [] = NONE
  | wrap_measures ctxt [f] =
      let
        val f' = Syntax.parse_term ctxt f
        val measure_const =
          Const (\<^const_name>\<open>Wellfounded.measure\<close>, dummyT)
      in
        SOME (Syntax.check_term ctxt (measure_const $ f'))
      end
  | wrap_measures ctxt fs =
      let
        val fs' = map (Syntax.parse_term ctxt) fs
        val list_term =
          fold_rev (fn t => fn acc =>
                       Const (\<^const_name>\<open>List.Cons\<close>, dummyT) $ t $ acc)
                   fs' (Const (\<^const_name>\<open>List.Nil\<close>, dummyT))
        val measures_const =
          Const (\<^const_name>\<open>List.measures\<close>, dummyT)
      in
        SOME (Syntax.check_term ctxt (measures_const $ list_term))
      end

datatype term_outcome =
    Proved of thm        (* totality theorem, ready for term_afterqed *)
  | DefaultFailed        (* default prover failed AND no metric supplied —
                            caller must error asking the user to supply
                            a BY_METRIC clause *)
  | MetricPartial of thm (* default prover failed, metric was supplied and
                            applied, but the metric path's internal sledge
                            could not close the remaining wf/decrease
                            obligations. The thm is the prepped state
                            (after resolve termination' + relation_infer),
                            with the wf + decrease subgoals exposed for
                            interactive discharge. FUN_DEBUG can push
                            this onto the minilang stack; plain FUN
                            errors out. *)

(* Termination dispatch.

   Stage 1 (always run): the default automatic termination prover
   (unless the debug config fun_fake_automatic_failure is set).
   Stage 2 (only if stage 1 fails and metric_strs ≠ []): the
   user-supplied metric path — resolve termination', instantiate via
   relation_infer_tac, close with sledge.

   Outcomes (caller decides what to do with each):
   - Stage 1 succeeds                    → Proved totality
   - Stage 1 fails, no metric            → DefaultFailed
   - Stage 1 fails, metric closes sledge → Proved totality
   - Stage 1 fails, metric path sledge
     couldn't close wf/decrease goals    → MetricPartial prepped
                                           (the state after resolve +
                                           relation_infer but before
                                           sledge, with the wf and
                                           decrease subgoals exposed)
   - Metric's prep tactic itself fails
     (resolve/relation_infer broken)     → error raised immediately *)
fun dispatch_term ctxt term_goal metric_strs =
  let
    val T = Config.get ctxt term_escalate_timeout
    fun try_prove tac =
      \<^try>\<open>
        SOME (Timeout.apply (Time.fromSeconds T)
               (fn () => Goal.prove ctxt [] [] term_goal (K tac)) ())
        catch _ => NONE\<close>

    (* Pre-generalize the function's termination rule so `?R` appears
       as a top-level schematic Var — this is what both the default
       prover and Function_Relation.relation_infer_tac need to have
       something to instantiate. *)
    val termination' =
      (case Function_Common.import_last_function ctxt of
         SOME {termination, ...} => Thm.forall_elim_vars 0 termination
       | NONE => error "FUN: no function data when dispatching termination")

    val default_tac =
      resolve_tac ctxt [termination'] 1 THEN
      Function_Common.termination_prover_tac false ctxt

    val default_result =
      if Config.get ctxt fun_fake_automatic_failure
      then NONE
      else try_prove default_tac
  in
    (case default_result of
       SOME thm => Proved thm
     | NONE =>
         (case wrap_measures ctxt metric_strs of
            NONE => DefaultFailed
          | SOME rel =>
              let
                (* Metric path (per plan): resolve termination' to
                   introduce the schematic ?R, let relation_infer_tac
                   instantiate it with the user-supplied
                   measure/measures term, then let
                   Phi_Sledgehammer_Solver.all_auto discharge the
                   remaining concrete wf and decrease obligations. *)
                val sledge_tac : tactic = fn st =>
                  if Config.get ctxt fun_fake_automatic_failure
                  then Seq.empty   (* debug: force metric path to fail *)
                  else
                  \<^try>\<open>
                    let
                      val (_, closed) =
                        Phi_Sledgehammer_Solver.all_auto
                          true                                (* improved version *)
                          Sledgehammer_Fact.no_fact_override  (* no extra facts *)
                          NONE                                (* no cache id *)
                          ctxt st
                    in Seq.single closed end
                    catch _ => Seq.empty\<close>
                val prep_tac =
                  resolve_tac ctxt [termination'] 1
                  THEN Function_Relation.relation_infer_tac ctxt rel 1
                val full_tac = prep_tac THEN sledge_tac
                (* Weaker, cheaper fallback closer used for both a
                   last-resort full attack and as a simplification
                   pass on the user-facing residual. Mirrors what
                   lexicographic_order_tac uses post-instantiation
                   (see lexicographic_order.ML:213-215). *)
                val termination_simps =
                  Named_Theorems.get ctxt \<^named_theorems>\<open>termination_simp\<close>
                val simp_tac = auto_tac (ctxt addsimps termination_simps)
                val fake_fail =
                  Config.get ctxt fun_fake_automatic_failure
              in
                (case try_prove full_tac of
                   SOME thm => Proved thm
                 | NONE =>
                     (* Sledge failed. Try auto+termination_simp as a
                        weaker closer; if it happens to finish the
                        proof, return Proved. Skipped entirely when
                        fun_fake_automatic_failure is set, so the
                        debug path simulates ALL automatic proving
                        (sledge + simp) failing at once. *)
                     (case if fake_fail
                            then NONE
                            else try_prove (prep_tac THEN simp_tac) of
                        SOME thm => Proved thm
                      | NONE =>
                          (* Neither sledge nor simp closed the
                             obligations. Compute a *simplified*
                             partial state for the user, so the
                             presented residual has had
                             auto+termination_simp already applied
                             (which typically closes `wf (measure f)`
                             and unfolds `(_, _) ∈ measure _` into
                             `_ < _`). If simp times out, fall back
                             to the raw state. Under
                             fun_fake_automatic_failure we also skip
                             this simplification so the user sees the
                             raw prep state. *)
                          let
                            val init_st =
                              Goal.init (Thm.cterm_of ctxt term_goal)
                            val prepped_opt =
                              if fake_fail
                              then run_with_timeout T prep_tac init_st
                              else
                                (case run_with_timeout T
                                       (prep_tac THEN simp_tac) init_st of
                                   SOME st => SOME st
                                 | NONE =>
                                     run_with_timeout T prep_tac init_st)
                          in
                            (case prepped_opt of
                               SOME st => MetricPartial st
                             | NONE =>
                                 error ("FUN: the BY_METRIC relation " ^
                                        "could not be applied to the " ^
                                        "termination goal " ^
                                        "(resolve/relation_infer failed)"))
                          end))
              end))
  end

(* Run phase 2 (termination). [outer_ctxt] is the body-state reference
   for Variable.restore_body; [lthy2] has body=false and is the
   post-partial-function context.

   Three outcomes from dispatch_term:
   - Proved: finalize via term_afterqed.
   - DefaultFailed: no metric supplied and default prover couldn't
     prove termination. Always error asking for BY_METRIC —
     open_on_fail is ignored because an untouched termination goal
     isn't actionable guidance for the user.
   - MetricPartial prepped: metric was supplied, the metric path's
     internal sledge couldn't close the prepped wf/decrease
     obligations. If open_on_fail, push the prepped state for
     interactive discharge; else error. *)
fun run_phase_2 outer_ctxt lthy2 {term_goal, term_afterqed}
                metric_strs open_on_fail post SK =
  (case dispatch_term lthy2 term_goal metric_strs of
     Proved totality =>
       let
         val lthy3 = term_afterqed [[totality]] lthy2
         val lthy3' = Variable.restore_body outer_ctxt lthy3 |> post
       in (lthy3', SK) end
   | DefaultFailed =>
       error ("FUN: the default termination prover failed to prove " ^
              "termination for this function. Please provide a " ^
              "BY_METRIC clause with a suitable measure (or " ^
              "measures) function, e.g.\n" ^
              "  FUN foo :: \"...\"\n" ^
              "    where \"...\"\n" ^
              "    BY_METRIC \"\<lambda>n. n\"")
   | MetricPartial prepped =>
       if not open_on_fail
       then error ("FUN: the default termination prover failed, and " ^
                   "the BY_METRIC relation did not fully close the " ^
                   "remaining well-foundedness / decrease obligations. " ^
                   "Use the FUN_DEBUG command to discharge them " ^
                   "interactively.")
       else
         let
           (* Restore outer body state BEFORE pushing; user's
              interactive minilang commands should see the natural
              body flag. *)
           val lthy_for_user = Variable.restore_body outer_ctxt lthy2
           (* Convert the raw prepped state into minilang's
              HOL.GOAL-wrapped shape so the HHF satisfies minilang's
              invariants. init_goal = iso_atomize + protect_goals;
              for our Pure-level termination goal iso_atomize is a
              no-op, so this is effectively just protect_goals. *)
           val init_st = init_goal lthy_for_user prepped
           fun term_cb ctxt_user (tstate, _, SK', _) =
             let
               val lthy2' = Variable.set_body false ctxt_user
               (* Follow HAVE's CB pattern: Goal.conclude strips the
                  Pure.prop wrapping, finalize_goal runs iso_rulify
                  (no-op here), Conjunction.elim_conjunctions splits
                  any conjunctions (we expect a single result). *)
               val lems =
                 Goal.conclude tstate
                 |> finalize_goal lthy2'
                 |> Conjunction.elim_conjunctions
               val totality =
                 case lems of
                   [th] => th
                 | _ => error ("FUN: unexpected number of theorems " ^
                               "from interactive termination proof")
               val lthy3 = term_afterqed [[totality]] lthy2'
               val lthy3' = Variable.restore_body outer_ctxt lthy3 |> post
             in (lthy3', SK') end
           (* Capture the outer HHF at push-time so PRINT can show
              both the deferred termination block and the outer
              proof goal, mirroring HAVE's PRT pattern. The stack
              invariant guarantees SK's head is an HHF. *)
           val (outer_st, outer_items) =
             case SK of
               HHF (st, items) :: _ => (st, items)
             | _ => raise BROKEN_INVARIANT
           fun term_prt _ t =
             BUNDL (outer_items,
                    [BLOCK t, print_stack [HHF (outer_st, outer_items)]])
           val _ = get_reporter () (Internal TERMINATION_PROOF_OPENED)
           (* Emit `Goals` with the actual residual termination subgoal
              terms so consumers (Python SubgoalMaker, translator's
              `(*goal: ...*)` annotations) see both the correct count
              and the correct contents.  Use `goals_of'` because `init_st`
              is in Minilang's protected form (`protect_goals` nests
              subgoals inside `HOL.GOAL` wrappers); `Thm.prems_of` would
              only walk the outer `Pure.imp` chain and under-count. *)
           val _ = get_reporter () (Goals (goals_of' init_st))
         in
           (lthy_for_user,
            HHF (init_st, empty_items)
            :: ENDBLK T_END
            :: MAGIC (term_cb, term_prt, NO_PARAM)
            :: SK)
         end)

(* Create simprocs that fire only on specific target terms.
   Each firing consumes the matched target from a mutable list, so the simproc
   fires at most once per indicated target. This prevents loops when the rule
   is structurally self-looping (the rewritten result contains a new aconv match). *)
fun thms_to_targeted_simprocs ctxt (entries: (thm * term list) list) : simproc list =
  let
    fun mk_targeted (i, (thm, targets)) =
      let
        val meta_rules = Raw_Simplifier.mksimps ctxt thm
        val remaining = Unsynchronized.ref targets
      in
        map_index (fn (j, rule) =>
          let
            val (lhs, _) = Logic.dest_equals
                  (Logic.strip_imp_concl (Thm.prop_of rule))
            fun proc _ ct =
              let val t = Thm.term_of ct
              in case find_first (fn tgt => Term.aconv (t, tgt)) (!remaining) of
                   SOME matched =>
                     (remaining := filter (fn tgt => not (Term.aconv (tgt, matched))) (!remaining);
                      SOME rule)
                 | NONE => NONE
              end
          in
            SOME (Simplifier.make_simproc ctxt
              { name = "targeted_simproc_" ^ string_of_int i ^ "_" ^ string_of_int j,
                lhss = [lhs],
                proc = K proc,
                identifier = [] })
          end handle TERM _ => NONE
        ) meta_rules
      end
  in map_filter I (flat (map_index mk_targeted entries)) end

(* After a function definition completes, check its .simps for looping
   rules and remove them from the simpset. The function remains defined
   and its .simps are still accessible by name. *)
fun remove_looping_simps lthy =
  case Function_Common.import_last_function lthy of
    SOME {simps = SOME simps, ...} =>
      let val cfg : Looping_Simp.config =
            {only_check_local = false, ignore_cond = false,
             local_ignore_cond = true, schematize_local_frees = true}
          val looping = filter (fn th =>
            Looping_Simp.simp_rule_may_loop cfg lthy (Thm.prop_of th)) simps
      in fold Simplifier.del_simp looping lthy end
  | _ => lthy

(* Extended FUN entrypoint. Runs phase 1 (pat-completeness) then phase 2
   (termination), with escalation + optional deferred-block handoff. *)
fun FUN_by_fun_ext fixes specs config metric_strs open_on_fail
                   (outer_ctxt, SK) =
  let
    val ctxt_fn = Variable.set_body false outer_ctxt
    (* DEBUG: check Ctr_Sugar for nat in both contexts *)
    val _ = let
      val trace_file = "/tmp/fun_debug_trace.txt"
      val has_sugar_outer = is_some (Ctr_Sugar.ctr_sugar_of outer_ctxt \<^type_name>\<open>nat\<close>)
      val has_sugar_fn = is_some (Ctr_Sugar.ctr_sugar_of ctxt_fn \<^type_name>\<open>nat\<close>)
      val suc_const = (case try (Proof_Context.read_const {proper = true, strict = false} outer_ctxt) "Suc" of
        SOME t => Syntax.string_of_term outer_ctxt t | NONE => "NOT FOUND")
      val eq_strs = map (fn ((_, eq), _, _) => eq) specs
      val msg = cat_lines ([
        "=== FUN_by_fun_ext DEBUG ===",
        "outer_ctxt has nat ctr_sugar: " ^ Bool.toString has_sugar_outer,
        "ctxt_fn has nat ctr_sugar: " ^ Bool.toString has_sugar_fn,
        "Suc resolves to: " ^ suc_const,
        "equations:"] @ eq_strs @ ["=== END ===", ""])
    in File.write (Path.explode trace_file) msg end
    fun post lthy = remove_looping_simps lthy
    val {pat_goal_state, pat_afterqed, lthy_after_prepare} =
      Proof_Local_Function.prepare_pat_goal fixes specs config false ctxt_fn
    val pat_state = escalate_pat lthy_after_prepare pat_goal_state
  in
    if Thm.nprems_of pat_state = 0
    then
      let
        val pat_thm = Goal.finish lthy_after_prepare pat_state
        val lthy2 = pat_afterqed [[pat_thm]] lthy_after_prepare
        val phase2 = Proof_Local_Function.prepare_term_goal lthy2
      in
        run_phase_2 outer_ctxt lthy2 phase2 metric_strs open_on_fail post SK
      end
    else if not open_on_fail
    then error ("FUN: the pattern-completeness/compatibility proof failed. " ^
                "Use the FUN_DEBUG command (or the ML-level FUN'' API with " ^
                "open_on_fail = true) to discharge the residual goals " ^
                "interactively.")
    else
      let
        val lthy_for_user =
          Variable.restore_body outer_ctxt lthy_after_prepare
        (* Convert the raw Goal.init'd pat-completeness state (which
           has shape `G1 ⟹ G2 ⟹ ... ⟹ Pure.prop C` with multiple
           Pure.imp premises) into minilang's HOL.GOAL-wrapped shape
           via init_goal (= iso_atomize + protect_goals). The
           matching un-wrap happens in pat_cb via
           Goal.conclude |> finalize_goal |> Conjunction.elim_conjunctions,
           mirroring HAVE's pattern and term_cb's pattern in run_phase_2. *)
        val pat_state_for_stack = init_goal lthy_for_user pat_state
        fun pat_cb ctxt_user (pstate, _, SK', _) =
          let
            val lthy1 = Variable.set_body false ctxt_user
            val lems =
              Goal.conclude pstate
              |> finalize_goal lthy1
              |> Conjunction.elim_conjunctions
            val pat_thm =
              case lems of
                [th] => th
              | _ => error ("FUN: unexpected number of theorems from " ^
                            "interactive pat-completeness proof")
            val lthy2 = pat_afterqed [[pat_thm]] lthy1
            val phase2 = Proof_Local_Function.prepare_term_goal lthy2
          in
            run_phase_2 outer_ctxt lthy2 phase2 metric_strs open_on_fail post SK'
          end
        (* Capture the outer HHF at push-time so PRINT can show both
           the deferred pat-completeness block and the outer proof
           goal, mirroring HAVE's PRT pattern. The stack invariant
           guarantees SK's head is an HHF. *)
        val (outer_st, outer_items) =
          case SK of
            HHF (st, items) :: _ => (st, items)
          | _ => raise BROKEN_INVARIANT
        fun pat_prt _ t =
          BUNDL (outer_items,
                 [BLOCK t, print_stack [HHF (outer_st, outer_items)]])
        val _ = get_reporter () (Internal PAT_COMPLETENESS_PROOF_OPENED)
        (* Same rationale as the termination-partial branch: emit the
           actual residual pat-completeness goal terms via `goals_of'`
           on the protected `pat_state_for_stack`. *)
        val _ = get_reporter () (Goals (goals_of' pat_state_for_stack))
      in
        (lthy_for_user,
         HHF (pat_state_for_stack, empty_items)
         :: ENDBLK T_END
         :: MAGIC (pat_cb, pat_prt, NO_PARAM)
         :: SK)
      end
  end

(* FUN runs add_fun_cmd which adds local-definition hyps to the proof
   context via Local_Defs.define. These hyps are discharged by
   Proof_Context.export at the nearest enclosing boundary — INTRO's
   subgoal cleanup, HAVE's block cleanup, or minilang's `conclude`
   export at the end of min_script. No local scope management is
   needed here. See the header of proof_local_function.ML for the
   full discussion of the result-discharge timing requirement. *)

(* ML-level API for agent use. Accepts metric and open_on_fail flags;
   min_script always passes {metric=[], open_on_fail=false} indirectly
   via the FUN_CMD parser. *)
fun FUN'' fixes specs {metric, open_on_fail} =
  fn ((ctxt, SK), TAB, ID) =>
    timed_OPR 60
      (FUN_by_fun_ext fixes specs Function_Fun.fun_config metric open_on_fail)
      ((ctxt, SK), TAB, ID)

(* BY_METRIC "term" (AND "term")*   —   optional trailing clause after
   the function specification. An empty list means no metric. *)
val metric_clause =
  Scan.optional
    (Parse.$$$ "BY_METRIC" |--
       (Parse.embedded_inner_syntax :::
          Scan.repeat (Parse.$$$ "AND" |-- Parse.embedded_inner_syntax)))
    []

(* Shared body between FUN and FUN_DEBUG: parses the function
   specification + optional BY_METRIC clause and dispatches to
   FUN_by_fun_ext with the given open_on_fail flag. *)
fun mk_FUN_CMD open_on_fail =
  Function_Common.function_parser Function_Fun.fun_config -- metric_clause
  >> (fn ((config, (fixes, specs)), metric_strs) =>
       fn ((ctxt, SK), TAB, ID) =>
         timed_OPR 60
           (FUN_by_fun_ext fixes specs config metric_strs open_on_fail)
           ((ctxt, SK), TAB, ID))

val FUN_CMD = mk_FUN_CMD false

(* FUN_DEBUG: same surface syntax as FUN, but routes through
   FUN_by_fun_ext with open_on_fail = true. A pat-completeness or
   termination residual is pushed onto the minilang stack as an HHF
   frame for interactive discharge, instead of erroring out. Exists
   primarily to exercise the Agent-interface code path from minilang
   scripts and to make the internal debug configs
   fun_fake_pat_completeness_failure / fun_fake_automatic_failure
   usable from min_script. *)
val FUN_DEBUG_CMD = mk_FUN_CMD true


(** CONFIG **)

(*TODO: items*)

datatype config = CFG_NOTE   of Thm.binding * (thm list * attribute list) list
                | CFG_BUNDLE of Bundle.name

fun CONFIG' prep_attr_thms raw_thms (ctxt, SK) =
  let val cfgs = prep_attr_thms ctxt raw_thms
      val timeout = Config.get ctxt mini_single_cmd_timeout
                 |> Time.fromMilliseconds
      val ctxt' =
            Timeout.apply timeout
                 (fold (fn CFG_BUNDLE name => Bundle.includes [name]
                         | CFG_NOTE   note => snd o Proof_Context.note_thms "" note) cfgs) ctxt
   in (ctxt', SK)
  end

val CONFIG   = timed_OPR 10 o CONFIG' (K I)
val CONFIG_FACTS'' = timed_OPR 10 o CONFIG' (fn ctxt =>
    let fun parse_fact ((b,attrs), facts) =
              ((b, map (Attrib.attribute_cmd ctxt) attrs),
               map (apfst (Proof_Context.get_fact ctxt)
                 #> apsnd (map (Attrib.attribute_cmd ctxt))) facts)
     in map (CFG_NOTE o parse_fact)
    end )
val CONFIG_BUNDL'' = timed_OPR 10 o CONFIG' (fn ctxt =>
    let fun parse name = CFG_BUNDLE (Bundle.check ctxt (name, Position.none))
     in map parse
    end )

val CONFIG_CMD = Parse_Spec.name_facts >> (
      timed_OPR 10 o CONFIG' (fn ctxt => fn facts =>
    let fun parse_fact ((b,attrs), facts) =
              ((b, map (Attrib.attribute_cmd ctxt) attrs),
               map (apfst (Proof_Context.get_fact ctxt)
                 #> apsnd (map (Attrib.attribute_cmd ctxt))) facts)
        fun parse (origin as ((b,[]), [(Facts.Named (name,_), [])])) =
              if Binding.is_empty b
              then CFG_BUNDLE (Bundle.check ctxt name)
              else CFG_NOTE (parse_fact origin)
          | parse fact = CFG_NOTE (parse_fact fact)
     in map parse facts
    end ))

(*** Toplevel ***)

(* Interfaces *)

val CMDS = Symtab.make [
      ("end",     END_CMD),
      ("next",    NXT_CMD),
      ("consider",CONSIDER_CMD),
      ("have",    HAVE_CMD),
      ("END",     END_CMD),
      ("NEXT",    NXT_CMD),
      ("CONSIDER",CONSIDER_CMD),
      ("HAVE",    HAVE_CMD),
      ("SUFFICES",SUFFICES_CMD),
      ("INST_VAR",INST_VAR_CMD),
      ("SPECIALIZE",SPECIALIZE_CMD),
      ("CASE_SPLIT", CASE_SPLIT_CMD),
      ("INDUCT",  INDUCT_CMD),
      ("SIMP" ,   SIMP_CMD),
      (* CRUSH disabled — currently broken *)
      ("SIMPLIFY", SIMPLIFY_CMD),
      ("INTRO",   INTRO_CMD),
      ("ALL_INTRO",INTRO_ALL_CMD),
      ("SPLIT_CONJS", SPLIT_CONJS_CMD),
      ("HAMMER",  HAMMER_CMD),
      ("PRINT",   PRINT_CMD),
      ("RULE",    RULE_CMD),
      ("LET",     LET_CMD),
      ("let",     LET_CMD),
      ("APPLY",   APPLY_CMD),
      ("apply",   APPLY_CMD),
      ("UNFOLD",  UNFOLD_CMD),
      ("CHOOSE",  CHOOSE_CMD),
      ("NOTATION",NOTATION_CMD),
      ("OPEN_MODULE", OPEN_MODULE_CMD),
      ("DEFINE",  DEFINE_CMD),
      ("FUN",     FUN_CMD),
      ("FUN_DEBUG", FUN_DEBUG_CMD),
      ("CONFIG",  CONFIG_CMD),
      ("STEP"  ,  STEP_CMD),
      ("CHAINING",CHAINING_CMD),
      ("SORRY" ,  END_or_NXT_by_SORRY_CMD),
      ("SORRY_NEXT",    SORRY_NEXT_CMD),
      ("SORRY_END_ALL", SORRY_END_ALL_CMD),
      ("SORRY_ONLY",    SORRY_ONLY_CMD)
    ]

val keywords = let open Keyword
      in empty_keywords
      |> add_keywords
         [ (("where", \<^here>), quasi_command_spec),
           (("::",    \<^here>), quasi_command_spec),
           ((":",     \<^here>), quasi_command_spec),
           ((",",     \<^here>), quasi_command_spec),
           (("and",   \<^here>), quasi_command_spec),
           (("in",   \<^here>), quasi_command_spec),
           (("when",  \<^here>), quasi_command_spec),
           (("if",    \<^here>), quasi_command_spec),
           (("obtains",\<^here>),quasi_command_spec),
           (("shows", \<^here>), quasi_command_spec),
           (("fixes", \<^here>), quasi_command_spec),
           (("defines",\<^here>),quasi_command_spec),
           (("shows", \<^here>), quasi_command_spec),
           (("constrains",\<^here>),quasi_command_spec),
           (("assumes",\<^here>),quasi_command_spec),
           (("notes", \<^here>), quasi_command_spec),
           (("includes",\<^here>),quasi_command_spec),
           (("|",     \<^here>), quasi_command_spec),
           (("(",     \<^here>), quasi_command_spec),
           ((")",     \<^here>), quasi_command_spec),
           (("[",     \<^here>), quasi_command_spec),
           (("]",     \<^here>), quasi_command_spec),
           (("?",     \<^here>), quasi_command_spec),
           (("=",     \<^here>), quasi_command_spec),
           (("for",   \<^here>), quasi_command_spec),
           (("WITH",  \<^here>), quasi_command_spec),
           (("WITHOUT",\<^here>),quasi_command_spec),
           (("IN",    \<^here>), quasi_command_spec),
           (("VARS",  \<^here>), quasi_command_spec),
           (("PREMISES", \<^here>), quasi_command_spec),
           (("infix",  \<^here>), quasi_command_spec),
           (("infixr", \<^here>), quasi_command_spec),
           (("infixl", \<^here>), quasi_command_spec),
           (("BY_METRIC", \<^here>), quasi_command_spec),
           (("AND",    \<^here>), quasi_command_spec),

           (("END",   \<^here>), command_spec (thy_end, [])),
           (("end",   \<^here>), command_spec (thy_end, [])),
           (("NEXT",  \<^here>), command_spec (thy_end, [])),
           (("SORRY", \<^here>), command_spec (thy_end, [])),
           (("SORRY_NEXT",    \<^here>), command_spec (thy_end, [])),
           (("SORRY_END_ALL", \<^here>), command_spec (thy_end, [])),
           (("SORRY_ONLY",   \<^here>), command_spec (prf_goal, [])),
           (("CONSIDER",\<^here>),command_spec (prf_asm_goal, [])),
           (("HAVE",  \<^here>), command_spec (prf_goal, [])),
           (("SUFFICES",\<^here>), command_spec (prf_goal, [])),
           (("INST_VAR",\<^here>), command_spec (prf_decl, [])),
           (("SPECIALIZE",\<^here>), command_spec (prf_decl, [])),
           (("CASE_SPLIT",  \<^here>), command_spec (prf_goal, [])),
           (("INDUCT",\<^here>), command_spec (prf_goal, [])),
           (* CRUSH disabled — currently broken *)
           (("SIMP" , \<^here>), command_spec (prf_goal, [])),
           (("SIMPLIFY", \<^here>), command_spec (prf_goal, [])),
           (("INTRO", \<^here>), command_spec (prf_goal, [])),
           (("ALL_INTRO", \<^here>), command_spec (prf_goal, [])),
           (("SPLIT_CONJS", \<^here>), command_spec (prf_goal, [])),
           (("HAMMER",\<^here>), command_spec (prf_goal, [])),
           (("PRINT", \<^here>), command_spec (diag,     [])),
           (("RULE",  \<^here>), command_spec (prf_decl, [])),
           (("LET",   \<^here>), command_spec (prf_decl, [])),
           (("APPLY", \<^here>), command_spec (prf_decl, [])),
           (("UNFOLD",\<^here>), command_spec (prf_goal, [])),
           (("CHOOSE",\<^here>), command_spec (prf_decl, [])),
           (("NOTATION",\<^here>), command_spec (prf_decl, [])),
           (("OPEN_MODULE",\<^here>), command_spec (prf_goal, [])),
           (("DEFINE",\<^here>), command_spec (prf_decl, [])),
           (("FUN",   \<^here>), command_spec (prf_decl, [])),
           (("FUN_DEBUG", \<^here>), command_spec (prf_decl, [])),
           (("CONFIG",\<^here>), command_spec (prf_decl, [])),
           (("STEP",  \<^here>), command_spec (prf_decl, [])),
           (("CHAINING", \<^here>), command_spec (prf_decl, []))
         ]
     end

fun lex_cmds source =
  let val pos = Position.make {
                  line=1, offset=1, end_offset=1,
                  props={label="", file="#MINSHELL SCRIPT", id="no_id"} }
      val src = Symbol_Pos.explode (source, pos)
      val toks = Token.tokenize keywords {strict = false} src

      fun split ret []  [] = ret
        | split ret buf [] = rev (Token.eof :: buf) :: ret
        | split ret buf (x::L) =
            if Token.is_command x
            then split (case buf of [] => ret
                           | _ => rev (Token.eof :: buf) :: ret) [x] L
            else if Token.is_ignored x
            then split ret buf L
            else split ret (x::buf) L

   in split [] [] toks
   |> rev
  end

fun parse_cmds toks =
  let val cmds = toks
              |> map (fn (h::toks) =>
                    case Symtab.lookup CMDS (Token.content_of h)
                      of SOME parser => fst (parser toks)
                       | NONE => error ("Bad Command " ^ Token.content_of h) )
   in fold I cmds
  end

fun conclude initial_ctxt ((ctxt', S  as [HHF (st',_)]),_,_) =
      let
        (* If FUN or similar extended the background theory, transfer
           initial_ctxt forward so export works (old thy ⊂ new thy) *)
        val initial_ctxt' =
          if Context.eq_thy (Proof_Context.theory_of initial_ctxt,
                             Proof_Context.theory_of ctxt')
          then initial_ctxt
          else Proof_Context.transfer (Proof_Context.theory_of ctxt') initial_ctxt
        val st'' = singleton (Proof_Context.export ctxt' initial_ctxt') st'
                  |> finalize_goal ctxt'
       in Pretty.writeln (pretty_tree ctxt' (print_stack S));
          st''
      end
  | conclude _ ((ctxt', S), _, _) =
     (Pretty.writeln (pretty_tree ctxt' (print_stack S));
      error "incomplete MINSHELL script")

fun PROVE tr ctxt st =
      INIT ctxt st
   |> OPR_NO_INCR (apfst INIT_SYNTAX)
   |> tr
   |> conclude ctxt

fun METHOD_i tr : Method.method = CONTEXT_METHOD (fn _ => fn (ctxt,st) =>
  if Thm.no_prems st
  then Seq.single (Seq.Result (ctxt, st))
  else Seq.make (fn () =>
      let val ret = PROVE tr ctxt st
          val ctxt' = Proof_Context.transfer (Thm.theory_of_thm ret) ctxt
       in SOME (Seq.Result (ctxt', ret), Seq.empty)
      end))

val METHOD = METHOD_i o parse_cmds o lex_cmds

val _ = Theory.setup (
  Method.setup \<^binding>\<open>min_script\<close> (
    Scan.peek (fn _ => Parse.embedded >> (fn src => fn _ =>
        METHOD src)))
  ""
)

end
