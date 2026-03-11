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

datatype ('term, 'thm, 'fact) command =
    UNFOLD   of 'fact list
  | WITNESS  of 'term list
  | RULE     of 'fact list
  | CASE_SPLIT of 'term (*target*) * Minilang.opt_var_names
                * 'thm option (*rule*)
  | INDUCT   of 'term (*target*) * Minilang.opt_var_names
              * 'term list (*arbitrary*) * 'thm option (*rule*)
  | NEXT_OR_END of 'fact list (*add lemmas*) * Minilang.opt_var_names
  | NEXT     of 'fact list (*add lemmas*) * Minilang.opt_var_names
  | END      of 'fact list (*add lemmas*)
  | BRANCH   of string list
  | HAVE     of string (*name*) * 'term (*statement*)
  | SUFFICES of 'term
  | OBTAIN   of (string * string option) list (*vars*) * string list (*constraints*)
  | SORRY    of Minilang.opt_var_names
  | HAMMER   of 'fact list (*with facts*)
  | INTRO    of bindings option
  | SIMPLIFY of 'fact list (*simp facts*) * bool (*use_system_simps*)
              * string list (*premise_names*) * bool (*simplify_goal*)
              * bindings option
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

exception INTRO_BINDINGS of {
    missing: bindings,
    auto_introduced: bindings,
    final: bindings
  }

val compute_bindings : Minilang.state -> string list -> string list -> bindings
val check_need_intro : Minilang.state -> bool

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

type counters = {
    prem_counter: int Synchronized.var,
    fact_counter: int Synchronized.var
  }
type config = cfg * budget * counters

datatype ('term, 'thm, 'fact) command =
    UNFOLD   of 'fact list
  | WITNESS  of 'term list
  | RULE     of 'fact list
  | CASE_SPLIT of 'term (*target*) * Minilang.opt_var_names
                * 'thm option (*rule*)
  | INDUCT   of 'term (*target*) * Minilang.opt_var_names
              * 'term list (*arbitrary*) * 'thm option (*rule*)
  | NEXT_OR_END of 'fact list (*add lemmas*) * Minilang.opt_var_names
  | NEXT     of 'fact list (*add lemmas*) * Minilang.opt_var_names
  | END      of 'fact list (*add lemmas*)
  | BRANCH   of string list
  | HAVE     of string (*name*) * 'term (*statement*)
  | SUFFICES of 'term
  | OBTAIN   of (string * string option) list (*vars*) * string list (*constraints*)
  | SORRY    of Minilang.opt_var_names
  | HAMMER   of 'fact list (*with facts*)
  | INTRO    of bindings option
  | SIMPLIFY of 'fact list (*simp facts*) * bool (*use_system_simps*)
              * string list (*premise_names*) * bool (*simplify_goal*)
              * bindings option
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
     #> REPL_Serialize.print_term printing_cfg ctxt'
    end

fun string_of_type ctxt =
    let val ctxt' = ctxt
              |> Config.put Printer.show_types false
              |> Config.put Printer.show_sorts false
              |> Config.put Printer.show_markup false
              |> Config.put Printer.show_structs false
              |> Config.put Printer.show_question_marks true
              |> Config.put Printer.show_brackets false
     in REPL_Serialize.print_typ printing_cfg ctxt'
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

(* Customized read functions with bound name deconfliction *)

fun read_term ctxt s =
  Syntax.read_term ctxt s
  |> Minilang.deconflict_bound_names ctxt

fun read_terms ctxt ss =
  Syntax.read_terms ctxt ss
  |> map (Minilang.deconflict_bound_names ctxt)

fun read_terms_with_type ctxt ss =
  map (fn (typ, raw_tm) =>
      Const ("_type_constraint_", typ --> typ)
        $ Syntax.parse_term ctxt raw_tm) ss
  |> Syntax.check_terms ctxt

fun read_prop ctxt s =
  Syntax.read_prop ctxt s
  |> Minilang.deconflict_bound_names ctxt

fun read_props ctxt ss =
  Syntax.read_props ctxt ss
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

fun AUTO_INTRO (counters:counters) (opt_bindings: bindings option) (s:Minilang.state)
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
    if not (Minilang.need_intro st) then
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
        val ((params', facts'), s') = Minilang.INTRO Minilang.SINGLE_GOAL minilang_var_names (SOME prem_names_for_intro) s

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
    if not (Minilang.need_intro st) then
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
fun check_need_intro (s:Minilang.state) : bool =
  let val st = Minilang.leading_proof_sequent_of s
   in Minilang.need_intro st
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
    val ((params', facts'), s') = (Minilang.SIMPLIFY_GOAL_AND_PREMISES
                                    simp_thms use_system_simps premise_names simplify_goal
                                    (SOME naming_prems_fn) (SOME naming_vars_fn)) s

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
  in
    s'
  end

fun interpret_i (config as (cfg, budget, counters)) cmd s =
  case cmd of
      SIMPLIFY (simp_facts, use_system_simps, premise_names, simplify_goal, user_bindings_opt) =>
        let val ctxt = Minilang.context_of s
            val simp_thms = maps (Attrib.eval_thms ctxt o single) simp_facts
         in AUTO_SIMPLIFY counters simp_thms use_system_simps premise_names
                          simplify_goal user_bindings_opt s
        end
    | UNFOLD facts =>
        let val _ = if null facts
                    then error "You must specify at least one theorem to unfold"
                    else ()
            val ctxt = Minilang.context_of s
            val defs = Attrib.eval_thms ctxt facts
        in Minilang.UNFOLD defs s
        end
    | WITNESS terms =>
        Minilang.CHOOSE terms s
    | RULE thms =>
        Minilang.RULE thms [] s
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
        Minilang.END_or_NXT vars {add=lemmas,del=[],only=false} s
    | NEXT (lemmas, vars) =>
        Minilang.NXT vars {add=lemmas,del=[],only=false} s
    | END lemmas =>
        Minilang.END {add=lemmas,del=[],only=false} s
    | BRANCH branches =>
        let val prem_ctr = #prem_counter counters
            val counter_start = Synchronized.value prem_ctr
            val (brs, final_counter) = fold_map (fn br => fn ctr =>
                  let val name = "premise" ^ string_of_int ctr
                  in (([], ([], [], [((Binding.name name, []), [(br, [])])])), ctr + 1)
                  end) branches counter_start
            val _ = Synchronized.change prem_ctr (K final_counter)
        in Minilang.CONSIDER brs s
        end
    | HAVE (name, goal) =>
        Minilang.HAVE'' [] [] [((Binding.name name, []), [(goal, [])])] s
    | SUFFICES goal =>
        Minilang.SUFFICES'' goal s
    | OBTAIN (vars, constraints) =>
        let val arg = [(map (fn (v,T) => (Binding.name v, T, NoSyn)) vars,
                       ([], [], map (fn goal => (Binding.empty_atts, [(goal, [])])) constraints))]
        in Minilang.CONSIDER arg s
        end
    | SORRY vars =>
        Minilang.END_or_NXT_by_SORRY vars s
    | HAMMER facts => (
        Minilang.HAMMER {add=facts,del=[],only=false} s
        handle Minilang.OPR_FAIL (Minilang.PROOF_FAIL, _) =>
          let
            val ctxt = Minilang.context_of s
            val st = Minilang.leading_proof_sequent_of s
                  |> Thm.prop_of
                  |> Logic.dest_implies |> fst
            val goal_str = string_of_term ctxt st
            val msg = "Failed to prove the proof goal automatically:\n  " ^ goal_str ^
                      "\nThe proof is non-trivial and you must provide a detailed proof."
          in
            raise Minilang.OPR_FAIL (Minilang.PROOF_FAIL, msg)
          end)
    | INTRO opt_bindings =>
        #2 (AUTO_INTRO counters opt_bindings s)
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
in
fun check_command_i s (SIMPLIFY (facts, use_sys, prems, simp_goal, bindings_opt)) =
      SIMPLIFY (map read_fact facts, use_sys, prems, simp_goal, bindings_opt)
  | check_command_i _ (RULE facts) = RULE (map read_fact facts)
  | check_command_i _ (UNFOLD facts) = UNFOLD (map read_fact facts)
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
  | check_command_i _ (NEXT_OR_END (facts, vars)) = NEXT_OR_END (map read_fact facts, vars)
  | check_command_i _ (NEXT (facts, vars)) = NEXT (map read_fact facts, vars)
  | check_command_i _ (END facts) = END (map read_fact facts)
  | check_command_i _ (BRANCH brs) = BRANCH brs
  | check_command_i s (HAVE (name, goal)) =
      let val ctxt = Minilang.context_of s
       in HAVE (name, read_prop ctxt goal)
      end
  | check_command_i s (SUFFICES goal) =
      let val ctxt = Minilang.context_of s
       in SUFFICES (read_prop ctxt goal)
      end
  | check_command_i _ (OBTAIN vc) = OBTAIN vc
  | check_command_i _ (SORRY vars) = SORRY vars
  | check_command_i _ (HAMMER facts) = HAMMER (map read_fact facts)
  | check_command_i _ (INTRO opt_bindings) = INTRO opt_bindings
  | check_command_i _ SKIP = SKIP

fun check_command s x = check_command_i s x
    handle ERROR msg => raise Minilang.OPR_FAIL (Minilang.TERMLANG, msg)

end

fun interpret cfg xcmd state =
  let val icmd = check_command state xcmd
   in interpret_i cfg icmd state
  end


end

