signature MINILANG_AGENT = sig

type budget = {
      QUERY_RET_LIMIT: int option,
      parallel_runs: int,
      total_timeout: Time.time option,
      step_limit: int
  }

type cfg = {
      drafting: bool,
      gussing_num_typ : bool
  }

type var_name = {internal_name: string, external_name: string, typ_pretty: string}
type prem_name = {internal_term: term, external_name: string, pretty: string}
type bindings = var_name list * prem_name list

datatype ('term, 'fact) extended_fact =
    FactByName of 'fact
  | FactInTime of 'term (*statement to prove on-the-fly*)

datatype ('term, 'thm, 'fact) command =
    UNFOLD   of ('term, 'fact) extended_fact list
  | WITNESS  of 'term list
  | RULE     of ('term, 'fact) extended_fact list
  | CASE_SPLIT of 'term (*target*) * Minilang.opt_var_names
                * 'thm option (*rule*)
  | INDUCT   of 'term (*target*) * Minilang.opt_var_names
              * 'term list (*arbitrary*) * 'thm option (*rule*)
  | NEXT_OR_END of ('term, 'fact) extended_fact list (*add lemmas*) * Minilang.opt_var_names
  | NEXT     of ('term, 'fact) extended_fact list (*add lemmas*) * Minilang.opt_var_names
  | END      of ('term, 'fact) extended_fact list (*add lemmas*)
  | BRANCH   of (string option * string) list
  | HAVE     of string (*name*) * 'term (*statement*) * bool (*auto_apply*)
  | SUFFICES of 'term
  | OBTAIN   of (string * string option) list (*vars*) * (string option * string) list (*constraints*)
  | SORRY_NEXT    of Minilang.opt_var_names
  | SORRY_END_ALL of Minilang.opt_var_names
  | SORRY_ONLY
  | HAMMER   of ('term, 'fact) extended_fact list (*with facts*) * int (*timeout in seconds*)
  | INTRO    of bindings option * bool (*split_conj*)
  | SIMPLIFY of ('term, 'fact) extended_fact list (*simp facts*) * bool (*use_system_simps*)
              * string list (*premise_names*) * bool (*simplify_goal*)
              * bindings option
  | SPECIALIZE of string (*result name*)
              * ('term, 'fact) extended_fact (*rule*)
              * (string * 'term) list (*instantiations: var_name * term*)
              * ('term, 'fact) extended_fact list (*facts to discharge*)
  | CHAINING of string option (*optional name; auto-generated if NONE*)
              * ('term, 'fact) extended_fact list (*facts to chain*)
  | DEFINE   of string (*function name*)
              * string option (*type expression, NONE = let Isabelle infer*)
              * string list (*equation clauses*)
              * string list (*BY_METRIC measures, [] = none*)
  | SKIP

type xcmd = (string, string, string) command
type icmd = (term, thm, Facts.ref * Token.src list) command

type counters = {
    prem_counter: int Synchronized.var,
    fact_counter: int Synchronized.var
  }
type config = cfg * budget * counters

val check_command : Minilang.state -> xcmd -> icmd
val interpret_i : config -> icmd -> Minilang.state -> Minilang.state
val interpret : config -> xcmd -> Minilang.state -> Minilang.state

val default_cfg : cfg * budget

exception FACT_IN_TIME_FAIL of term
exception INTRO_BINDINGS of {
    missing: bindings,
    auto_introduced: bindings,
    final: bindings
  }
exception SIMPLIFY_FALLBACK_NOSYS
exception SIMPLIFY_FALLBACK_ONCE_SIMPROC
(* (fact_name, pretty_printed_proposition) list — the derived facts produced by SPECIALIZE *)
exception SPECIALIZE_RESULT of (string * string) list
(* (function_name, pretty_type) — emitted after DEFINE so the Python side
   knows the inferred type when the user omitted the type field. *)
exception DEFINE_RESULT of string * string

val compute_bindings : Minilang.state -> string list -> string list -> bindings
val check_need_intro : bool -> Minilang.state -> bool

(* Classify a proven theorem and register it into the automatic reasoners
   (simpset / classical intro/elim set / splitter) that apply. Used by
   operations that opt into automatic propagation of their resulting fact.

   `auto_apply_attrib` is the ML-level attribute. It is also registered at
   theory load time under the name `mini_auto_apply` so it can be referenced
   from a `Token.src` when emitting binding attributes to Minilang.HAVE''. *)
val classify_thm : Proof.context -> thm -> string list
val auto_apply_attrib : attribute

val string_of_term : Proof.context -> term -> string
val string_of_type : Proof.context -> typ -> string
val string_of_type_full_sort : Proof.context -> typ -> string

val read_term : Proof.context -> string -> term
val read_terms : Proof.context -> string list -> term list
val read_terms_with_type : Proof.context -> (typ * string) list -> term list
val read_prop : Proof.context -> string -> term
val read_props : Proof.context -> string list -> term list

end

structure MiniLang_Agent : MINILANG_AGENT = struct

type budget = {
      QUERY_RET_LIMIT: int option,
      parallel_runs: int,
      total_timeout: Time.time option,
      step_limit: int
  }

type cfg = {
      drafting: bool,
      gussing_num_typ : bool
  }

val default_cfg : (cfg * budget) = ({
      drafting = true,
      gussing_num_typ = true
    }, {
      QUERY_RET_LIMIT = SOME 30,
      parallel_runs = 1,
      total_timeout = SOME (Time.fromSeconds 600),
      step_limit = 30
    })

type var_name = {internal_name: string, external_name: string, typ_pretty: string}
type prem_name = {internal_term: term, external_name: string, pretty: string}
type bindings = var_name list * prem_name list

exception INTRO_BINDINGS of {
    missing: bindings,
    auto_introduced: bindings,
    final: bindings
  }
exception SIMPLIFY_FALLBACK_NOSYS
exception SIMPLIFY_FALLBACK_ONCE_SIMPROC
(* (fact_name, pretty_printed_proposition) list — the derived facts produced by SPECIALIZE *)
exception SPECIALIZE_RESULT of (string * string) list
exception DEFINE_RESULT of string * string

type counters = {
    prem_counter: int Synchronized.var,
    fact_counter: int Synchronized.var
  }
type config = cfg * budget * counters

datatype ('term, 'fact) extended_fact =
    FactByName of 'fact
  | FactInTime of 'term

datatype ('term, 'thm, 'fact) command =
    UNFOLD   of ('term, 'fact) extended_fact list
  | WITNESS  of 'term list
  | RULE     of ('term, 'fact) extended_fact list
  | CASE_SPLIT of 'term (*target*) * Minilang.opt_var_names
                * 'thm option (*rule*)
  | INDUCT   of 'term (*target*) * Minilang.opt_var_names
              * 'term list (*arbitrary*) * 'thm option (*rule*)
  | NEXT_OR_END of ('term, 'fact) extended_fact list (*add lemmas*) * Minilang.opt_var_names
  | NEXT     of ('term, 'fact) extended_fact list (*add lemmas*) * Minilang.opt_var_names
  | END      of ('term, 'fact) extended_fact list (*add lemmas*)
  | BRANCH   of (string option * string) list
  | HAVE     of string (*name*) * 'term (*statement*) * bool (*auto_apply*)
  | SUFFICES of 'term
  | OBTAIN   of (string * string option) list (*vars*) * (string option * string) list (*constraints*)
  | SORRY_NEXT    of Minilang.opt_var_names
  | SORRY_END_ALL of Minilang.opt_var_names
  | SORRY_ONLY
  | HAMMER   of ('term, 'fact) extended_fact list (*with facts*) * int (*timeout in seconds*)
  | INTRO    of bindings option * bool (*split_conj*)
  | SIMPLIFY of ('term, 'fact) extended_fact list (*simp facts*) * bool (*use_system_simps*)
              * string list (*premise_names*) * bool (*simplify_goal*)
              * bindings option
  | SPECIALIZE of string (*result name*)
              * ('term, 'fact) extended_fact (*rule*)
              * (string * 'term) list (*instantiations: var_name * term*)
              * ('term, 'fact) extended_fact list (*facts to discharge*)
  | CHAINING of string option (*optional name; auto-generated if NONE*)
              * ('term, 'fact) extended_fact list (*facts to chain*)
  | DEFINE   of string (*function name*)
              * string option (*type expression, NONE = let Isabelle infer*)
              * string list (*equation clauses*)
              * string list (*BY_METRIC measures, [] = none*)
  | SKIP

type xcmd = (string, string, string) command
type icmd = (term, thm, Facts.ref * Token.src list) command

(* Pretty printing configuration *)
val printing_cfg = {all_typ=false, bv_typ=true, constant_typ=false, free_typ=false, num_typ=true,
                    sorting=false, show_sort_P=NONE, show_type_P=NONE}

fun string_of_term ctxt =
    let val ctxt' = ctxt
              |> Config.put Printer.show_types false
              |> Config.put Printer.show_sorts false
              |> Config.put Printer.show_markup false
              |> Config.put Printer.show_structs false
              |> Config.put Printer.show_question_marks true
              |> Config.put Printer.show_brackets false
     in Object_Logic.atomize_term ctxt'
     #> Minilang.deconflict_bound_names ctxt'
     #> RPC_Pretty.print_term printing_cfg ctxt'
    end

fun string_of_type ctxt =
    let val ctxt' = ctxt
              |> Config.put Printer.show_types false
              |> Config.put Printer.show_sorts false
              |> Config.put Printer.show_markup false
              |> Config.put Printer.show_structs false
              |> Config.put Printer.show_question_marks true
              |> Config.put Printer.show_brackets false
     in RPC_Pretty.print_typ printing_cfg ctxt'
    end

fun string_of_type_full_sort ctxt =
    let val ctxt' = ctxt
              |> Config.put Printer.show_types true
              |> Config.put Printer.show_sorts true
              |> Config.put Printer.show_markup false
              |> Config.put Printer.show_structs false
              |> Config.put Printer.show_question_marks true
              |> Config.put Printer.show_brackets false
     in Syntax.string_of_typ ctxt'
     #> REPL.trim_makrup
    end

fun string_of_thm ctxt th = string_of_term ctxt (Thm.prop_of th)

(* Unwrap Par_Exn: if all inner exceptions are ERROR, merge into one ERROR.
   Syntax.read_prop/read_term use Par_List.map_independent internally, which wraps
   exceptions in Par_Exn via release_all. This prevents handle ERROR from matching. *)
fun release_par_error exn =
  (case Par_Exn.dest exn of
    SOME exns =>
      let val msgs = map_filter (fn ERROR msg => SOME msg | _ => NONE) exns
      in if null exns orelse length msgs <> length exns
         then Exn.reraise exn
         else error (String.concatWith "\n" msgs)
      end
  | NONE => Exn.reraise exn)

(* Customized read functions with bound name deconfliction *)

fun read_term ctxt s =
  \<^try>\<open>Syntax.read_term ctxt s
   catch exn => release_par_error exn\<close>
  |> Minilang.deconflict_bound_names ctxt

fun read_terms ctxt ss =
  \<^try>\<open>Syntax.read_terms ctxt ss
   catch exn => release_par_error exn\<close>
  |> map (Minilang.deconflict_bound_names ctxt)

fun read_terms_with_type ctxt ss =
  map (fn (typ, raw_tm) =>
      Const ("_type_constraint_", typ --> typ)
        $ Syntax.parse_term ctxt raw_tm) ss
  |> (fn ts => \<^try>\<open>Syntax.check_terms ctxt ts
       catch exn => release_par_error exn\<close>)

fun read_prop ctxt s =
  \<^try>\<open>Syntax.read_prop ctxt s
   catch exn => release_par_error exn\<close>
  |> Minilang.deconflict_bound_names ctxt

fun read_props ctxt ss =
  \<^try>\<open>Syntax.read_props ctxt ss
   catch exn => release_par_error exn\<close>
  |> map (Minilang.deconflict_bound_names ctxt)

(* Extract types of leading existential quantifiers from a goal *)
fun extract_leading_ex_types goal =
  let
    fun strip_ex (Const(\<^const_name>\<open>Trueprop\<close>, _) $ t) = strip_ex t
      | strip_ex (Const(\<^const_name>\<open>Ex\<close>, Type(_, [T, _])) $ Abs (_, var_T, body)) =
          var_T :: strip_ex body
      | strip_ex (Const(\<^const_name>\<open>Ex1\<close>, Type(_, [T, _])) $ Abs (_, var_T, body)) =
          var_T :: strip_ex body
      | strip_ex (Const(\<^const_name>\<open>Set.Bex\<close>, _) $ _ $ Abs (_, var_T, body)) =
          var_T :: strip_ex body
      | strip_ex _ = []
  in strip_ex goal
  end

(* Extract types from the leading goal of a state *)
fun get_witness_types s =
  let val st = Minilang.leading_proof_sequent_of s
      val goal = Thm.major_prem_of st
   in extract_leading_ex_types goal
  end

fun AUTO_INTRO (counters:counters) (opt_bindings: bindings option) (split_conj: bool) (s:Minilang.state)
  : bindings * Minilang.state =
  let
    val ctxt = Minilang.context_of s
            |> Config.put Printer.show_markup false
    val st = Minilang.leading_proof_sequent_of s

    (* Extract provided bindings, use empty lists if NONE *)
    val (provided_var_names, provided_prem_names) = the_default ([], []) opt_bindings

    (* Flag: whether to report missing bindings *)
    val report_missing = is_some opt_bindings
  in
    (* Step 1: Check if INTRO is applicable *)
    if not (Minilang.need_intro split_conj st) then
      (([], []), s)
    else
      let
        (* Step 2: Extract quantified variables and premises from goal *)
        val goal_term = Thm.prop_of st
                    |> Logic.dest_implies |> fst
                    |> Minilang.deconflict_bound_names ctxt
        val (vars, prems, _) = Minilang.strip_meta_and_hol_hhf goal_term

        (* Step 3: Process variables - try to match with provided names, auto-generate if not found *)
        val (var_bindings, matched_var_names, _) =
          let
            (* For each quantified variable in goal, try to find a match in provided names *)
            val (bindings_with_flags, _) =
              fold_map (fn (internal_name, var_ty) => fn name_ctx =>
                case find_first (fn {internal_name = pn, ...} => pn = internal_name) provided_var_names of
                  SOME {external_name, ...} =>
                    (* Matched: use provided external name *)
                    let val (actual_name, name_ctx') = Minilang_Aux.variant_name external_name name_ctx
                     in (((internal_name, actual_name, var_ty), SOME external_name), name_ctx')
                    end
                | NONE =>
                    (* Not matched: auto-generate using internal name *)
                    let val (actual_name, name_ctx') = Minilang_Aux.variant_name internal_name name_ctx
                     in (((internal_name, actual_name, var_ty), NONE), name_ctx')
                    end
              ) vars (Variable.names_of ctxt)

            val names = map (#2 o fst) bindings_with_flags
            val (_, ctxt') = Variable.add_fixes names ctxt
            val matched = map_filter snd bindings_with_flags

            val bindings = map (fn ((in_name, ex_name, ty), _) =>
                             {internal_name = in_name,
                              external_name = ex_name,
                              typ_pretty = string_of_type ctxt' ty})
                           bindings_with_flags
           in (bindings, matched, ctxt')
          end

        (* Convert var_bindings to opt_var_names for Minilang.INTRO *)
        val minilang_var_names = SOME (map (SOME o #external_name) var_bindings)

        (* Step 4: Process premises - try to match with provided names, auto-generate if not found *)
        val prem_counter = #prem_counter counters
        val (prem_names_for_intro, matched_prem_terms) =
          let
            val counter_start = Synchronized.value prem_counter
            (* For each premise in goal, try to find a match in provided names *)
            val (names_with_flags, final_counter) =
              fold_map (fn prem_term => fn counter_val =>
                case find_first (fn {internal_term, ...} => internal_term aconv prem_term) provided_prem_names of
                  SOME {external_name, ...} =>
                    (* Matched: use provided external name *)
                    ((SOME external_name, SOME prem_term), counter_val)
                | NONE =>
                    (* Not matched: auto-generate name using counter *)
                    let val name = "premise" ^ string_of_int counter_val
                     in ((SOME name, NONE), counter_val + 1)
                    end
              ) prems counter_start

            val _ = Synchronized.change prem_counter (K final_counter)
            val matched = map_filter snd names_with_flags
           in (map fst names_with_flags, matched)
          end

        (* Step 5: Call INTRO with SINGLE_GOAL mode and get the items it fixed *)
        val ((params', facts'), s') = Minilang.INTRO Minilang.SINGLE_GOAL (SOME split_conj) minilang_var_names (SOME prem_names_for_intro) s

        (* Step 6: Extract context from the new state *)
        val ctxt' = Minilang.context_of s'

        (* Step 7: Build var_bindings and prem_bindings with pretty printing from new context *)
        val var_bindings_final = map2 (fn {internal_name, external_name, ...} => fn (_, ty) =>
                                         {internal_name = internal_name,
                                          external_name = external_name,
                                          typ_pretty = string_of_type ctxt' ty})
                                       var_bindings params'

        val prem_bindings_final = map2 (fn prem_term => fn (name, prop) =>
                                         {internal_term = prem_term,
                                          external_name = name,
                                          pretty = string_of_term ctxt' prop})
                                       prems facts'

        (* Step 8: Compute missing bindings (provided but not used in goal) *)
        (* Only report variables where external_name != internal_name *)
        val missing_vars = if report_missing
          then filter (fn {internal_name, external_name, ...} =>
                 external_name <> internal_name andalso
                 not (member (op =) (map fst vars) internal_name)) provided_var_names
          else []

        (* For premises, report all missing bindings *)
        val missing_prems = if report_missing
          then filter (fn {internal_term, ...} =>
                 not (exists (fn p => p aconv internal_term) prems)) provided_prem_names
          else []

        (* Step 9: Compute auto-introduced bindings (in goal but not matched with provided) *)
        val auto_vars = filter (fn {internal_name, ...} =>
                          not (member (op =) matched_var_names internal_name))
                        var_bindings_final

        val auto_prems = filter (fn {internal_term, ...} =>
                           not (exists (fn t => t aconv internal_term) matched_prem_terms))
                         prem_bindings_final

        (* Step 10: Send INTRO_BINDINGS message with three fields *)
        val _ = Minilang.get_reporter () (Minilang.Internal (INTRO_BINDINGS {
          missing = (missing_vars, missing_prems),
          auto_introduced = (auto_vars, auto_prems),
          final = (var_bindings_final, prem_bindings_final)
        }))

        (* Step 11: Return results *)
      in
        ((var_bindings_final, prem_bindings_final), s')
      end
  end

(* Compute bindings for the leading proof goal by binding provided names in order *)
fun compute_bindings (s:Minilang.state) (var_names: string list) (fact_names: string list)
  : bindings =
  let
    val ctxt = Minilang.context_of s
              |> Config.put Printer.show_markup false
    val st = Minilang.leading_proof_sequent_of s
  in
    (* Check if there's a quantified goal *)
    if not (Minilang.need_intro false st) then
      ([], [])
    else
      let
        (* Extract quantified variables and premises from goal *)
        val goal_term = Thm.prop_of st |> Logic.dest_implies |> fst
                     |> Minilang.deconflict_bound_names ctxt
        val (vars, prems, _) = Minilang.strip_meta_and_hol_hhf goal_term

        (* Check length constraints *)
        val num_vars = length vars
        val num_prems = length prems
        val num_var_names = length var_names
        val num_fact_names = length fact_names

        val _ = if num_var_names <> num_vars
                then raise Minilang.OPR_FAIL (Minilang.INVALID_OPR,
                       "Expected " ^ string_of_int num_vars ^ " variable name(s), but got " ^
                       string_of_int num_var_names)
                else ()

        val _ = if num_fact_names <> num_prems
                then raise Minilang.OPR_FAIL (Minilang.INVALID_OPR,
                       "Expected " ^ string_of_int num_prems ^ " fact name(s), but got " ^
                       string_of_int num_fact_names)
                else ()

        (* Bind variables in order: var_names[i] -> vars[i] *)
        val var_bindings =
          let
            val pairs = ListPair.zip (var_names, vars)
            val names = map fst pairs
            val (_, ctxt') = Variable.add_fixes names ctxt
           in map (fn (ex_name, (in_name, ty)) =>
                    {internal_name = in_name,
                     external_name = ex_name,
                     typ_pretty = string_of_type ctxt' ty})
                  pairs
          end

        (* Bind premises in order: fact_names[j] -> prems[j] *)
        val prem_bindings =
          let
            val pairs = ListPair.zip (fact_names, prems)
           in map (fn (ex_name, prem_term) =>
                    {internal_term = prem_term,
                     external_name = ex_name,
                     pretty = string_of_term ctxt prem_term})
                  pairs
          end
      in
        (var_bindings, prem_bindings)
      end
  end

(* Check if the leading proof goal needs INTRO (i.e., has quantified variables or premises) *)
fun check_need_intro consider_conj (s:Minilang.state) : bool =
  let val st = Minilang.leading_proof_sequent_of s
   in Minilang.need_intro consider_conj st
  end

fun AUTO_SIMPLIFY
    (counters: counters)
    (simp_thms: thm list)
    (use_system_simps: bool)
    (premise_names: string list)
    (simplify_goal: bool)
    (user_bindings_opt: bindings option)
    (s: Minilang.state)
    : Minilang.state =
  let
    val ctxt = Minilang.context_of s
    val prem_counter = #prem_counter counters

    (* Extract provided bindings, use empty lists if NONE *)
    val (provided_var_names, provided_prem_names) = the_default ([], []) user_bindings_opt
    val report_bindings = is_some user_bindings_opt

    (* Track matched premise bindings during naming function execution *)
    val matched_prem_terms_ref = Unsynchronized.ref []
    val matched_var_names_ref = Unsynchronized.ref []
    val vars_before_ref = Unsynchronized.ref ([] : (string * typ) list)
    val prems_before_ref = Unsynchronized.ref ([] : term list)

    (* Variable naming function: batch process all variables with deconfliction *)
    fun naming_vars_fn (vars: (string * typ) list) : string list =
      let
        (* Store the vars for later use *)
        val _ = vars_before_ref := vars

        (* Use fold_map to thread name context through all variables *)
        val (names, _) = fold_map (fn (var_name, var_ty) => fn name_ctx =>
          case find_first (fn {internal_name, ...} => internal_name = var_name) provided_var_names of
            SOME {external_name, ...} =>
              let val (actual_name, name_ctx') = Minilang_Aux.variant_name external_name name_ctx
                  val _ = matched_var_names_ref := var_name :: !matched_var_names_ref
              in (actual_name, name_ctx')
              end
          | NONE =>
              (* Auto-generate using internal name with deconfliction *)
              let val (actual_name, name_ctx') = Minilang_Aux.variant_name var_name name_ctx
              in (actual_name, name_ctx')
              end
        ) vars (Variable.names_of ctxt)
      in names
      end

    (* Premise naming function: batch process all premises *)
    fun naming_prems_fn (prem_terms: term list) : string list =
      Synchronized.change_result prem_counter (fn counter_start =>
        let
          (* Store the prem_terms for later use *)
          val _ = prems_before_ref := prem_terms

          (* Use fold_map to thread counter through all premises *)
          val (names, final_counter) = fold_map (fn prem_term => fn counter_val =>
            case find_first (fn {internal_term, ...} => internal_term aconv prem_term) provided_prem_names of
              SOME {external_name, ...} =>
                let val _ = matched_prem_terms_ref := prem_term :: !matched_prem_terms_ref
                in (external_name, counter_val)
                end
            | NONE =>
                (* Auto-generate name using counter *)
                let val name = "premise" ^ string_of_int counter_val
                in (name, counter_val + 1)
                end
          ) prem_terms counter_start
        in
          (names, final_counter)
        end)

    (* Execute SIMPLIFY with both naming functions - call operation *)
    val simplify_timeout = SOME (Time.fromSeconds 10)

    (* Detect self-looping user rules and partition them *)
    val thy = Proof_Context.theory_of ctxt
    fun thm_loops thm =
      exists (fn meta_eq =>
        let val (lhs, rhs) = Logic.dest_equals
                (Logic.strip_imp_concl (Thm.prop_of meta_eq))
        in Minilang.simp_rule_loops thy (lhs, rhs) end
        handle TERM _ => false)
      (Raw_Simplifier.mksimps ctxt thm)
    val (looping_thms, safe_thms) = List.partition thm_loops simp_thms
    val has_looping = not (null looping_thms)
    val base_simp_thms = if has_looping then safe_thms else simp_thms

    fun do_simplify thms simprocs use_sys =
      (Minilang.SIMPLIFY_GOAL_AND_PREMISES
        thms simprocs use_sys premise_names simplify_goal
        (SOME naming_prems_fn) (SOME naming_vars_fn) simplify_timeout) s

    fun mk_base_simprocs () =
      if has_looping then Minilang.thms_to_once_simprocs ctxt looping_thms
      else []

    fun mk_all_once () = Minilang.thms_to_once_simprocs ctxt simp_thms

    val (((params', facts'), s'), fell_back_nosys, fell_back_once) =
      if use_system_simps
      then (do_simplify base_simp_thms (mk_base_simprocs ()) true, false, false)
           handle Timeout.TIMEOUT _ =>
             ((do_simplify base_simp_thms (mk_base_simprocs ()) false, true, false)
              handle Timeout.TIMEOUT _ =>
                ((do_simplify [] (mk_all_once ()) false, true, true)
                 handle Timeout.TIMEOUT _ =>
                   raise Minilang.OPR_FAIL (Minilang.PROOF_FAIL,
                     "Simplification timed out. The rewriting rules may cause an infinite loop.")))
      else (do_simplify base_simp_thms (mk_base_simprocs ()) false, false, false)
           handle Timeout.TIMEOUT _ =>
             ((do_simplify [] (mk_all_once ()) false, false, true)
              handle Timeout.TIMEOUT _ =>
                raise Minilang.OPR_FAIL (Minilang.PROOF_FAIL,
                  "Simplification timed out. The rewriting rules may cause an infinite loop."))

    (* Always build and report bindings *)
    val _ =
      let
        val ctxt' = Minilang.context_of s'
        val matched_prem_terms = !matched_prem_terms_ref
        val matched_var_names = !matched_var_names_ref

        (* Build final variable bindings from params' returned by SIMPLIFY *)
        val var_bindings_final =
          map2 (fn (internal_name, _) => fn (external_name, ty) =>
            {internal_name = internal_name,
             external_name = external_name,
             typ_pretty = string_of_type ctxt' ty})
          (!vars_before_ref) params'

        (* Build final premise bindings from facts' returned by SIMPLIFY *)
        val prem_bindings_final =
          map2 (fn prem_term => fn (name, exterm) =>
            {internal_term = prem_term,
             external_name = name,
             pretty = string_of_term ctxt' exterm})
          (!prems_before_ref) facts'

        (* Compute missing variable bindings - provided but not in vars_before *)
        val missing_vars =
          if report_bindings then
            filter (fn {internal_name, ...} =>
              not (exists (fn (vn, _) => vn = internal_name) (!vars_before_ref))) provided_var_names
          else []

        (* Compute missing premise bindings - provided but not in prems_before *)
        val missing_prems =
          if report_bindings then
            filter (fn {internal_term, ...} =>
              not (exists (fn prem_term => prem_term aconv internal_term) (!prems_before_ref))) provided_prem_names
          else []

        (* Compute auto-introduced variables - not matched during naming *)
        val auto_vars =
          if report_bindings then
            filter (fn {internal_name, ...} =>
              not (member (op =) matched_var_names internal_name))
            var_bindings_final
          else []

        (* Compute auto-introduced premises - not matched during naming *)
        val auto_prems =
          if report_bindings then
            filter (fn {internal_term, ...} =>
              not (exists (fn t => t aconv internal_term) matched_prem_terms))
            prem_bindings_final
          else []

        (* Always report via INTRO_BINDINGS exception *)
        val _ = Minilang.get_reporter () (Minilang.Internal (INTRO_BINDINGS {
          missing = (missing_vars, missing_prems),
          auto_introduced = (auto_vars, auto_prems),
          final = (var_bindings_final, prem_bindings_final)
        }))
      in () end

    val _ = if fell_back_nosys
            then Minilang.get_reporter ()
                   (Minilang.Internal SIMPLIFY_FALLBACK_NOSYS)
            else ()
    val _ = if fell_back_once
            then Minilang.get_reporter ()
                   (Minilang.Internal SIMPLIFY_FALLBACK_ONCE_SIMPROC)
            else ()
  in
    s'
  end

exception FACT_IN_TIME_FAIL of term

type counter = int Unsynchronized.ref
fun mk_counter () = Unsynchronized.ref 0

(* Resolve FactInTime: prove the statement, register in context, return FactByName.
   FactByName passes through unchanged. Threads updated context via fold. *)
fun pre_resolve_fact _ (FactByName fref) ctxt = (fref, ctxt)
  | pre_resolve_fact counter (FactInTime prop) ctxt =
      let val goal = Goal.init (Thm.cterm_of ctxt prop)
          val proved =
            (case Seq.pull (Phi_Sledgehammer_Solver.fast_mepo_tac (Time.fromSeconds 3) ctxt 1 goal)
               of SOME (st', _) => st'
                | NONE => raise FACT_IN_TIME_FAIL prop)
            handle ERROR _ => raise FACT_IN_TIME_FAIL prop
          val thm = Goal.finish ctxt proved
          val i = !counter
          val _ = counter := i + 1
          val fact_name = "proven_in_time___" ^ string_of_int i
          val ((_, _), ctxt') = Proof_Context.note_thms ""
                ((Binding.name fact_name, []), [([thm], [])]) ctxt
      in ((Facts.Named ((fact_name, Position.none), NONE), []), ctxt') end

fun pre_resolve_facts counter ctxt facts =
  fold_map (pre_resolve_fact counter) facts ctxt

(* Resolve extended facts to a flat thm list (for SIMPLIFY, UNFOLD) *)
fun resolve_to_thms counter ctxt facts =
  let val (refs, ctxt') = pre_resolve_facts counter ctxt facts
  in maps (Attrib.eval_thms ctxt' o single) refs
  end

(* Resolve extended facts to fact refs, threading context (for RULE, HAMMER, END, NXT) *)
fun resolve_to_refs ctxt facts = pre_resolve_facts ctxt facts

fun resolve_to_override counter ctxt facts =
  let val (refs, ctxt') = resolve_to_refs counter ctxt facts
  in (ctxt', {add = refs, del = [], only = false}) end

(* Resolve extended facts and update Minilang state's context *)
fun with_resolved_refs counter s facts f =
  let val ctxt = Minilang.context_of s
      val (refs, ctxt') = resolve_to_refs counter ctxt facts
      val s' = Minilang.map_context (K ctxt') s
  in f s' refs end

fun with_resolved_override counter s facts f =
  let val ctxt = Minilang.context_of s
      val (ctxt', ovr) = resolve_to_override counter ctxt facts
      val s' = Minilang.map_context (K ctxt') s
  in f s' ovr end

(* Resolve the defining session of a Const by looking up its entry in the
   consts name space, then reading the first dotted component of the owning
   theory's long name (e.g. "HOL.List" → "HOL"). *)
fun session_of_const ctxt (Const (c, _)) =
      (let val space = Consts.space_of (Proof_Context.consts_of ctxt)
           val {theory_long_name, ...} = Name_Space.the_entry space c
        in case Long_Name.explode theory_long_name of
             [] => NONE
           | s :: _ => SOME s
       end handle ERROR _ => NONE)
  | session_of_const _ _ = NONE

fun is_user_predicate ctxt t =
  case session_of_const ctxt (Term.head_of t) of
    SOME s => s <> "HOL" andalso s <> "Pure"
  | NONE => false

(* An intro rule in the user's sense: the theorem has at least one premise,
   and the head of the conclusion is a constant whose defining session is
   neither HOL nor Pure. *)
fun chk_user_intro ctxt th =
  let val prop = Thm.prop_of th
      val concl = Logic.strip_assums_concl prop
      val prems = Logic.strip_assums_hyp prop
      val concl' = case concl of \<^Const>\<open>Trueprop\<close> $ t => t | t => t
   in not (null prems) andalso is_user_predicate ctxt concl' end

fun classify_thm ctxt th =
  let val is_intro = chk_user_intro ctxt th
      val kinds = []
      val kinds = if Phi_Sledgehammer_Solver.chk_elim th
                    then "elim" :: kinds else kinds
      val kinds = if Phi_Sledgehammer_Solver.chk_split th
                    then "split" :: kinds else kinds
      val kinds = if is_intro then "intro" :: kinds else kinds
      (* Per spec: intro ⇒ also register as simp. Independent equations also
         qualify as simp rules. *)
      val kinds = if is_intro orelse
                     Phi_Sledgehammer_Solver.chk_simp (Thm.prop_of th)
                    then "simp" :: kinds else kinds
   in kinds end

(* Attribute form of the classifier. Runs at `note_thmss` time (i.e. once the
   fact has actually been proven and is being bound into the context), which
   is the only point where the `thm` is stable. Classifies the theorem and
   directly registers it into the underlying simpset / classical set / split
   set via the corresponding ML APIs — no round-trip through the attribute
   name table, which would be both wasteful and fragile. *)
val auto_apply_attrib : attribute =
  Thm.declaration_attribute (fn th => fn context =>
    let val pctxt = Context.proof_of context
        val kinds = classify_thm pctxt th
        fun apply_kind "simp"  = Simplifier.map_ss (Raw_Simplifier.add_simp th)
          | apply_kind "split" = Simplifier.map_ss (Splitter.add_split th)
          | apply_kind "intro" =
              (fn ctx => the_default ctx
                           (#1 (Classical.unsafe_intro NONE (ctx, th))))
          | apply_kind "elim"  =
              (fn ctx => the_default ctx
                           (#1 (Classical.unsafe_elim NONE (ctx, th))))
          | apply_kind _       = I
     in fold apply_kind kinds context
    end)

fun interpret_i (config as (cfg, budget, counters)) cmd s =
  case cmd of
      SIMPLIFY (simp_facts, use_system_simps, premise_names, simplify_goal, user_bindings_opt) =>
        let val ctxt = Minilang.context_of s
            val simp_thms = resolve_to_thms (mk_counter ()) ctxt simp_facts
         in AUTO_SIMPLIFY counters simp_thms use_system_simps premise_names
                          simplify_goal user_bindings_opt s
        end
    | UNFOLD facts =>
        let val _ = if null facts
                    then error "You must specify at least one theorem to unfold"
                    else ()
            val ctxt = Minilang.context_of s
            val defs = resolve_to_thms (mk_counter ()) ctxt facts
        in Minilang.UNFOLD defs s
        end
    | WITNESS terms =>
        Minilang.CHOOSE terms s
    | RULE facts =>
        with_resolved_refs (mk_counter ()) s facts (fn s' => fn refs =>
          Minilang.RULE refs [] s')
    | CASE_SPLIT (target, vars, rule) =>
        Minilang.CASE_SPLIT (false, ([[SOME target]], rule)) vars [] s
    | INDUCT (target, vars, arbitrary, rule) =>
        let val ctxt = Minilang.context_of s
            val vs = map (fn Free nt => nt
                           | x => error ("The `arbitrary` argument must be variables, but (" ^
                                         string_of_term ctxt x ^ ") is given.")) arbitrary
        in Minilang.INDUCT
                    (false, ([[SOME (NONE, (target, false))]], (([vs], []), Option.map single rule))) vars [] s
        end
    | NEXT_OR_END (lemmas, vars) =>
        with_resolved_override (mk_counter ()) s lemmas (fn s' => fn ovr =>
          Minilang.END_or_NXT vars ovr s')
    | NEXT (lemmas, vars) =>
        with_resolved_override (mk_counter ()) s lemmas (fn s' => fn ovr =>
          Minilang.NXT vars ovr s')
    | END lemmas =>
        with_resolved_override (mk_counter ()) s lemmas (fn s' => fn ovr =>
          Minilang.END ovr s')
    | BRANCH branches =>
        let val prem_ctr = #prem_counter counters
            val counter_start = Synchronized.value prem_ctr
            val (brs, final_counter) = fold_map (fn (name_opt, br) => fn ctr =>
                  let val (name, ctr') = case name_opt of
                          SOME n => (n, ctr)
                        | NONE => ("premise" ^ string_of_int ctr, ctr + 1)
                  in (([], ([], [], [((Binding.name name, []), [(br, [])])])), ctr')
                  end) branches counter_start
            val _ = Synchronized.change prem_ctr (K final_counter)
        in Minilang.CONSIDER brs s
        end
    | HAVE (name, goal, auto_apply) =>
        let val attr_srcs = if auto_apply
              then [Token.make_src ("mini_auto_apply", Position.none) []]
              else []
         in Minilang.HAVE'' [] []
              [((Binding.name name, attr_srcs), [(goal, [])])] s
        end
    | SUFFICES goal =>
        Minilang.SUFFICES'' goal s
    | OBTAIN (vars, constraints) =>
        let val prem_ctr = #prem_counter counters
            val counter_start = Synchronized.value prem_ctr
            val (named_constraints, final_counter) = fold_map (fn (name_opt, goal) => fn ctr =>
                  let val (name, ctr') = case name_opt of
                          SOME n => (n, ctr)
                        | NONE => ("premise" ^ string_of_int ctr, ctr + 1)
                  in (((Binding.name name, []), [(goal, [])]), ctr')
                  end) constraints counter_start
            val _ = Synchronized.change prem_ctr (K final_counter)
            val arg = [(map (fn (v,T) => (Binding.name v, T, NoSyn)) vars,
                       ([], [], named_constraints))]
        in Minilang.CONSIDER arg s
        end
    | SORRY_NEXT vars =>
        Minilang.SORRY_NEXT vars s
    | SORRY_END_ALL vars =>
        Minilang.SORRY_END_ALL vars s
    | SORRY_ONLY =>
        Minilang.SORRY_ONLY s
    | HAMMER (facts, timeout) => (
        with_resolved_override (mk_counter ()) s facts (fn s' => fn ovr =>
          let val ctxt = Minilang.context_of s'
              val improved_SH = Config.get ctxt Minilang.mini_use_improved_SH
              val override' = if improved_SH then ovr
                              else Sledgehammer_Fact.no_fact_override
              val prover = fn id => Phi_Sledgehammer_Solver.auto_raw
                             improved_SH override' id (SOME (Time.fromSeconds timeout))
          in Minilang.HAMMER prover s'
          end)
        handle Phi_Sledgehammer_Solver.Auto_Fail reason =>
          let val msg = case reason
                of Phi_Sledgehammer_Solver.Subgoal_Fail sub =>
                     "Automatic proof fails on the subgoal:\n  " ^
                     string_of_term (Minilang.context_of s) sub ^
                     "\nThe goal is non-trivial and a step-by-step proof is required."
                 | _ => "Automatic proof fails. The goal is non-trivial and a step-by-step proof is required."
          in raise Minilang.OPR_FAIL (Minilang.PROOF_FAIL, msg)
          end
             | Minilang.OPR_FAIL (Minilang.PROOF_FAIL, _) =>
          raise Minilang.OPR_FAIL (Minilang.PROOF_FAIL,
            "Automatic proof fails. The goal is non-trivial and a step-by-step proof is required."))
    | INTRO (opt_bindings, split_conj) =>
        #2 (AUTO_INTRO counters opt_bindings split_conj s)
    | SPECIALIZE (name, rule_fact, insts, discharge_facts) =>
        let val ctxt = Minilang.context_of s
            val rule_thms = resolve_to_thms (mk_counter ()) ctxt [rule_fact]
            val discharge_thms = resolve_to_thms (mk_counter ()) ctxt discharge_facts
            (* "?x" or "?x.1" specifically targets a schematic variable (parsed via
               Lexicon.read_variable; error if not schematic);
               bare "x" is auto-classified by inst_universal_quantifiers
               (schematic > Pure.all > HOL.All). *)
            val all_schematic_vars =
                  maps (fn r => Term.add_var_names (Thm.prop_of r) []) rule_thms
            val insts' = map (fn (n, tm) =>
              if String.isPrefix "?" n then
                let val idx = case Lexicon.read_variable n
                      of SOME xi => xi
                       | NONE => raise Minilang.OPR_FAIL (Minilang.INVALID_OPR,
                                   "Specialize: cannot parse variable name " ^ quote n)
                in if member (op =) all_schematic_vars idx then (idx, tm)
                   else raise Minilang.OPR_FAIL (Minilang.INVALID_OPR,
                               "Variable " ^ n ^ " is not found in the rule")
                end
              else ((n, 0), tm)) insts
            val facts_before = Minilang.get_local_facts s
            val s' = Minilang.SPECIALIZE'' (SOME name) rule_thms insts' discharge_thms s
                     handle ERROR msg => raise Minilang.OPR_FAIL (Minilang.INVALID_OPR,
                               REPL.trim_makrup msg)
            val facts_after = Minilang.get_local_facts s'
            val ctxt' = Minilang.context_of s'
            (* Compute newly introduced facts as (fact_name, pretty_expression) pairs *)
            val new_facts = filter (fn (n, _) =>
                  not (exists (fn (n', _) => n = n') facts_before)) facts_after
            val result = map (fn (n, t) => (n, string_of_term ctxt' t)) new_facts
            val _ = Minilang.get_reporter ()
                      (Minilang.Internal (SPECIALIZE_RESULT result))
        in s'
        end
    | CHAINING (name_opt, facts) =>
        with_resolved_refs (mk_counter ()) s facts (fn s' => fn refs =>
          let val ctxt' = Minilang.context_of s'
              val thms = maps (Attrib.eval_thms ctxt' o single) refs
              val facts_before = Minilang.get_local_facts s'
              val s'' = Minilang.CHAINING name_opt thms s'
              val facts_after = Minilang.get_local_facts s''
              val new_facts = filter (fn (n, _) =>
                    not (exists (fn (n', _) => n = n') facts_before)) facts_after
              val ctxt'' = Minilang.context_of s''
              val result = map (fn (n, t) => (n, string_of_term ctxt'' t)) new_facts
              val _ = Minilang.get_reporter ()
                        (Minilang.Internal (SPECIALIZE_RESULT result))
           in s''
          end)
    | DEFINE (name, ty_opt, equations, metric) =>
        let
          val fixes : (binding * string option * mixfix) list =
            [(Binding.name name, ty_opt, NoSyn)]
          val specs : Specification.multi_specs_cmd =
            map (fn eq => ((Binding.empty_atts, eq), [], [])) equations
          val s' = Minilang.FUN'' fixes specs
                     {metric = metric, open_on_fail = true} s
          (* Report the function's type so the Python side can update
             Define._fixed_vars_at_me / _after_me even when the user
             omitted the type field. *)
          val ctxt' = Minilang.context_of s'
          val ty_str =
            case Function_Common.import_last_function ctxt' of
              SOME {fs = f :: _, ...} =>
                Syntax.string_of_typ ctxt' (fastype_of f)
            | _ => the_default "?" ty_opt
          val _ = Minilang.get_reporter ()
                    (Minilang.Internal (DEFINE_RESULT (name, ty_str)))
        in s' end
    | SKIP => s

local 
val keywords = Thy_Header.get_keywords @{theory Pure}
fun read_fact src =
  let val symbols = Input.source_explode (Input.string src)
      val toks = Token.tokenize keywords {strict = true} symbols
              |> filter Token.is_proper
   in case Scan.read Token.stopper Parse.thm toks
        of SOME fact => fact
         | NONE => error ("Cannot parse \"" ^ src ^ "\" as a fact reference")
  end

fun read_thms ctxt src =
  let val fact = read_fact src
   in Attrib.eval_thms ctxt [fact]
  end

fun chk_single _ _ [x] = x
  | chk_single ctxt rule lst = error ("Expect exact one rule but \"" ^ the rule
        ^ "\" refers to the following facts:\n"
        ^ String.concat (map (fn th => "- " ^ string_of_thm ctxt th ^ "\n") lst)
        ^ "You may select the i-th rule by using \"" ^ the rule ^ "(i)\".")

fun check_extended_fact ctxt (FactByName name) = FactByName (read_fact name)
  | check_extended_fact ctxt (FactInTime stmt) = FactInTime (read_prop ctxt stmt)

in
fun check_command_i s (SIMPLIFY (facts, use_sys, prems, simp_goal, bindings_opt)) =
      let val ctxt = Minilang.context_of s
      in SIMPLIFY (map (check_extended_fact ctxt) facts, use_sys, prems, simp_goal, bindings_opt) end
  | check_command_i s (RULE facts) =
      let val ctxt = Minilang.context_of s
      in RULE (map (check_extended_fact ctxt) facts) end
  | check_command_i s (UNFOLD facts) =
      let val ctxt = Minilang.context_of s
      in UNFOLD (map (check_extended_fact ctxt) facts) end
  | check_command_i s (WITNESS terms) =
      let val ctxt = Minilang.context_of s
          val typs = get_witness_types s
          val num_typs = length typs
          val num_terms = length terms
          val _ = if num_typs = num_terms then ()
                  else
                    let val msg =
                          if num_typs = 0 andalso num_terms = 1 then
                            "The proof goal is not led by an existential quantification"
                          else if num_typs = 0 then
                            "The proof goal is not led by existential quantifications"
                          else
                            String.concat [
                              "Insufficient existential quantifications: the goal has ",
                              string_of_int num_typs,
                              " leading existential quantifier",
                              if num_typs = 1 then "" else "s",
                              " but ",
                              string_of_int num_terms,
                              " witness term",
                              if num_terms = 1 then " was" else "s were",
                              " provided"
                            ]
                     in raise Minilang.OPR_FAIL (Minilang.INVALID_OPR, msg)
                    end
          val typed_terms = ListPair.zip (typs, terms)
       in WITNESS (read_terms_with_type ctxt typed_terms)
      end
  | check_command_i s (CASE_SPLIT (target, vars, rule)) =
      let val ctxt = Minilang.context_of s
          val rule' = Option.map (chk_single ctxt rule o read_thms ctxt) rule
          val target' = read_term ctxt target
       in CASE_SPLIT (target', vars, rule')
      end
  | check_command_i s (INDUCT (target, vars, arbitrary, rule)) =
      let val ctxt = Minilang.context_of s
          val (target' :: arbitrary') = read_terms ctxt (target :: arbitrary)
          val rule' = Option.map (chk_single ctxt rule o read_thms ctxt) rule
       in INDUCT (target', vars, arbitrary', rule')
      end
  | check_command_i s (NEXT_OR_END (facts, vars)) =
      let val ctxt = Minilang.context_of s
      in NEXT_OR_END (map (check_extended_fact ctxt) facts, vars) end
  | check_command_i s (NEXT (facts, vars)) =
      let val ctxt = Minilang.context_of s
      in NEXT (map (check_extended_fact ctxt) facts, vars) end
  | check_command_i s (END facts) =
      let val ctxt = Minilang.context_of s
      in END (map (check_extended_fact ctxt) facts) end
  | check_command_i _ (BRANCH brs) = BRANCH brs (*name_opt * string passthrough*)
  | check_command_i s (HAVE (name, goal, auto_apply)) =
      let val ctxt = Minilang.context_of s
       in HAVE (name, read_prop ctxt goal, auto_apply)
      end
  | check_command_i s (SUFFICES goal) =
      let val ctxt = Minilang.context_of s
       in SUFFICES (read_prop ctxt goal)
      end
  | check_command_i _ (OBTAIN vc) = OBTAIN vc (*name_opt * string passthrough*)
  | check_command_i _ (SORRY_NEXT vars) = SORRY_NEXT vars
  | check_command_i _ (SORRY_END_ALL vars) = SORRY_END_ALL vars
  | check_command_i _ SORRY_ONLY = SORRY_ONLY
  | check_command_i s (HAMMER (facts, timeout)) =
      let val ctxt = Minilang.context_of s
      in HAMMER (map (check_extended_fact ctxt) facts, timeout) end
  | check_command_i _ (INTRO opt_bindings) = INTRO opt_bindings
  | check_command_i s (SPECIALIZE (name, rule_fact, insts, discharge_facts)) =
      let val ctxt = Minilang.context_of s
          val (names, raws) = ListPair.unzip insts
          val terms = read_terms ctxt raws
      in SPECIALIZE (name,
                     check_extended_fact ctxt rule_fact,
                     names ~~ terms,
                     map (check_extended_fact ctxt) discharge_facts)
      end
  | check_command_i s (CHAINING (name_opt, facts)) =
      let val ctxt = Minilang.context_of s
      in CHAINING (name_opt, map (check_extended_fact ctxt) facts) end
  | check_command_i _ (DEFINE d) = DEFINE d
    (* strings passthrough — Minilang.FUN'' parses them internally *)
  | check_command_i _ SKIP = SKIP

fun check_command s x = check_command_i s x
    handle ERROR msg => raise Minilang.OPR_FAIL (Minilang.TERMLANG, msg)

end

fun interpret cfg xcmd state =
  let val icmd = check_command state xcmd
   in interpret_i cfg icmd state
  end

(* Register `auto_apply_attrib` under the name `mini_auto_apply` so that the
   HAVE branch (and any other operation that wants the same treatment) can
   reference it via a Token.src when emitting binding attributes to Minilang
   operations that pass through `Attrib.attribute_cmd` at note-time. *)
val _ = Theory.setup
  (Attrib.setup \<^binding>\<open>mini_auto_apply\<close>
     (Scan.succeed auto_apply_attrib)
     "classify a proven fact and register it into the applicable automatic \
     \reasoners (simp / intro / elim / split)")

end

