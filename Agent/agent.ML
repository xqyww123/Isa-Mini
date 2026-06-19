signature MINILANG_AGENT = sig

type budget = {
      timeout_seconds: int,
      max_tool_calls: int,
      max_retries: int
  }

type cfg = {
      auto_interpret_for_embedding: bool option
  }

type var_name = {internal_name: string, external_name: string, typ_pretty: string}
type prem_name = {internal_term: term, external_name: string, pretty: string}
type bindings = var_name list * prem_name list

datatype ('term, 'fact) extended_fact =
    FactByName of 'fact
  | FactInTime of string (*assigned name*) * 'term (*statement to prove on-the-fly*)

datatype ('term, 'thm, 'fact) command =
    UNFOLD   of ('term, 'fact) extended_fact list
  | WITNESS  of 'term list
  | RULE     of ('term, 'fact) extended_fact list
              * (string * string) list list (*post-rule schematic instantiation rounds:
                            each round a list of (var-name, value-string) pairs;
                            same shape in xcmd and icmd, parsed at interpret time*)
  | CASE_SPLIT of 'term (*target*) * Minilang.opt_var_names
                * 'thm option (*rule*) * bool (*no_simp*)
                * (string * string) list list (*post-rule schematic instantiation rounds*)
  | INDUCT   of 'term (*target*) * Minilang.opt_var_names
              * 'term list (*arbitrary*)
              * 'fact list (*facts_to_generalize: in xcmd a raw name string; in
                            icmd a resolved `Facts.ref * Token.src list` — the
                            standard agent fact-ref path (see `read_fact`).
                            Supports `h`, `h(i)`, `h(1-3)`, `h[attr]`. *)
              * 'thm option (*rule*) * bool (*no_simp*)
              * (string * string) list list (*post-rule schematic instantiation rounds*)
  | NEXT_OR_END of ('term, 'fact) extended_fact list (*add lemmas*) * Minilang.opt_var_names
  | NEXT     of ('term, 'fact) extended_fact list (*add lemmas*) * Minilang.opt_var_names
  | END      of ('term, 'fact) extended_fact list (*add lemmas*)
  | BRANCH   of (string option * string) list
  | HAVE     of string (*name*)
             * (string * string option) list (*fixes: var_name × type_string_opt*)
             * (string option * string) list (*assumes: premise_name_opt × prop_string*)
             * string (*conclusion*)
             * bool (*auto_apply*)
  | SUFFICES of (string * string option) list (*fixes*)
             * (string option * string) list (*assumes*)
             * string (*conclusion*)
  | OBTAIN   of (string * string option) list (*vars*) * (string option * string) list (*constraints*)
  | SORRY_NEXT    of Minilang.opt_var_names
  | SORRY_END_ALL of Minilang.opt_var_names
  | SORRY_ONLY
  | HAMMER   of ('term, 'fact) extended_fact list (*with facts*) * int (*timeout in seconds*)
              * (string * int) option (*cached proof: method_string * time_ms; NONE = no cache*)
  | INTRO    of bindings option
  | SPLIT_CONJS
  | SIMPLIFY of (('term, 'fact) extended_fact * term list option) list (*simp facts with optional targets*)
              * bool (*use_system_simps*)
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
  | CONTRADICTION of string (*hypothesis_binding_name*)
  | SETUP_REWRITING of string (*name, from Python*)
                    * (string * string option) list (*for_any: var_name × type_string_opt*)
                    * (string option * string) list (*conditions: name_opt × prop_string*)
                    * string (*redex*) * string (*residue*)
  | COMPUTE of string (*result name*) * 'term (*term to evaluate*)

type xcmd = (string, string, string) command
type icmd = (term, thm, Facts.ref * Token.src list) command

datatype exec_mode = LIVE | REPLAY

type counters = {
    prem_counter: int Synchronized.var
  }
type config = cfg * budget * counters * exec_mode

val check_command : Minilang.state -> xcmd -> icmd
val interpret_i : config -> icmd -> Minilang.state -> Minilang.state
val interpret : config -> xcmd -> Minilang.state -> Minilang.state

(* Replay post-rule schematic instantiation rounds on the post-rule state,
   folding Minilang.INST_GOAL_VARS over the (var-name, value-string) rounds.
   Each round is split by leading-"'" into type insts and term insts. *)
val apply_post_insts : (string * string) list list -> Minilang.state -> Minilang.state

val default_cfg : cfg * budget

exception FACT_IN_TIME_FAIL of term
exception INTRO_BINDINGS of {
    missing: bindings,
    auto_introduced: bindings,
    final: bindings
  }
exception SIMPLIFY_FALLBACK_NOSYS
exception SIMPLIFY_FALLBACK_ONCE_SIMPROC
exception SIMPLIFY_TARGETS_STALE of string list (* names of discarded rules *)
(* (fact_name, pretty_printed_proposition) list — the derived facts produced by SPECIALIZE *)
exception SPECIALIZE_RESULT of (string * string) list
(* (function_name, pretty_type) — emitted after DEFINE so the Python side
   knows the inferred type when the user omitted the type field. *)
exception DEFINE_RESULT of string * string
exception SETUP_REWRITING_MAY_LOOP
exception COMPUTE_RESULT of string * string

val compute_bindings : Minilang.state -> string list -> string list -> bindings
val check_need_intro : Minilang.state -> bool

(* Classify a proven theorem and register it into the automatic reasoners
   (simpset / classical intro/elim set / splitter) that apply. Used by
   operations that opt into automatic propagation of their resulting fact.

   `auto_apply_attrib` is the ML-level attribute. It is also registered at
   theory load time under the name `mini_auto_apply` so it can be referenced
   from a `Token.src` when emitting binding attributes to Minilang.HAVE''. *)
val classify_thm : Proof.context -> thm -> string list
val auto_apply_attrib : attribute

val string_of_term : Proof.context -> term -> string
val string_of_term_main_syntax : term -> string
val string_of_type : Proof.context -> typ -> string
val string_of_type_full_sort : Proof.context -> typ -> string
val string_of_sort : Proof.context -> sort -> string

val read_term : Proof.context -> string -> term
val read_term_abbrev : Proof.context -> string -> term
val read_terms : Proof.context -> string list -> term list
val read_terms_with_type : Proof.context -> (typ * string) list -> term list
val read_prop : Proof.context -> string -> term
val read_props : Proof.context -> string list -> term list
val read_thms : Proof.context -> string -> thm list

end

structure MiniLang_Agent : MINILANG_AGENT = struct

type budget = {
      timeout_seconds: int,
      max_tool_calls: int,
      max_retries: int
  }

type cfg = {
      auto_interpret_for_embedding: bool option
  }

val default_cfg : cfg * budget = ({auto_interpret_for_embedding = NONE}, {
      timeout_seconds = 14400,
      max_tool_calls = 10000,
      max_retries = 8
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
exception SIMPLIFY_TARGETS_STALE of string list
(* (fact_name, pretty_printed_proposition) list — the derived facts produced by SPECIALIZE *)
exception SPECIALIZE_RESULT of (string * string) list
exception DEFINE_RESULT of string * string
exception SETUP_REWRITING_MAY_LOOP
exception COMPUTE_RESULT of string * string

datatype exec_mode = LIVE | REPLAY

type counters = {
    prem_counter: int Synchronized.var
  }
type config = cfg * budget * counters * exec_mode

datatype ('term, 'fact) extended_fact =
    FactByName of 'fact
  | FactInTime of string * 'term

datatype ('term, 'thm, 'fact) command =
    UNFOLD   of ('term, 'fact) extended_fact list
  | WITNESS  of 'term list
  | RULE     of ('term, 'fact) extended_fact list
              * (string * string) list list (*post-rule schematic instantiation rounds:
                            each round a list of (var-name, value-string) pairs;
                            same shape in xcmd and icmd, parsed at interpret time*)
  | CASE_SPLIT of 'term (*target*) * Minilang.opt_var_names
                * 'thm option (*rule*) * bool (*no_simp*)
                * (string * string) list list (*post-rule schematic instantiation rounds*)
  | INDUCT   of 'term (*target*) * Minilang.opt_var_names
              * 'term list (*arbitrary*)
              * 'fact list (*facts_to_generalize: in xcmd a raw name string; in
                            icmd a resolved `Facts.ref * Token.src list` — the
                            standard agent fact-ref path (see `read_fact`).
                            Supports `h`, `h(i)`, `h(1-3)`, `h[attr]`. *)
              * 'thm option (*rule*) * bool (*no_simp*)
              * (string * string) list list (*post-rule schematic instantiation rounds*)
  | NEXT_OR_END of ('term, 'fact) extended_fact list (*add lemmas*) * Minilang.opt_var_names
  | NEXT     of ('term, 'fact) extended_fact list (*add lemmas*) * Minilang.opt_var_names
  | END      of ('term, 'fact) extended_fact list (*add lemmas*)
  | BRANCH   of (string option * string) list
  | HAVE     of string (*name*)
             * (string * string option) list (*fixes: var_name × type_string_opt*)
             * (string option * string) list (*assumes: premise_name_opt × prop_string*)
             * string (*conclusion*)
             * bool (*auto_apply*)
  | SUFFICES of (string * string option) list (*fixes*)
             * (string option * string) list (*assumes*)
             * string (*conclusion*)
  | OBTAIN   of (string * string option) list (*vars*) * (string option * string) list (*constraints*)
  | SORRY_NEXT    of Minilang.opt_var_names
  | SORRY_END_ALL of Minilang.opt_var_names
  | SORRY_ONLY
  | HAMMER   of ('term, 'fact) extended_fact list (*with facts*) * int (*timeout in seconds*)
              * (string * int) option (*cached proof: method_string * time_ms; NONE = no cache*)
  | INTRO    of bindings option
  | SPLIT_CONJS
  | SIMPLIFY of (('term, 'fact) extended_fact * term list option) list (*simp facts with optional targets*)
              * bool (*use_system_simps*)
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
  | CONTRADICTION of string (*hypothesis_binding_name*)
  | SETUP_REWRITING of string (*name, from Python*)
                    * (string * string option) list (*for_any: var_name × type_string_opt*)
                    * (string option * string) list (*conditions: name_opt × prop_string*)
                    * string (*redex*) * string (*residue*)
  | COMPUTE of string (*result name*) * 'term (*term to evaluate*)

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
     in Object_Logic.atomize_term ctxt'
     #> Minilang.deconflict_bound_names
     #> RPC_Pretty.print_term printing_cfg ctxt'
    end

val string_of_term_main_syntax =
    string_of_term (Proof_Context.init_global @{theory Main})

fun string_of_type ctxt =
    let val ctxt' = ctxt
              |> Config.put Printer.show_types false
              |> Config.put Printer.show_sorts false
              |> Config.put Printer.show_markup false
              |> Config.put Printer.show_structs false
              |> Config.put Printer.show_question_marks true
     in RPC_Pretty.print_typ printing_cfg ctxt'
    end

fun string_of_type_full_sort ctxt =
    let val ctxt' = ctxt
              |> Config.put Printer.show_types true
              |> Config.put Printer.show_sorts true
              |> Config.put Printer.show_markup false
              |> Config.put Printer.show_structs false
              |> Config.put Printer.show_question_marks true
     in Syntax.string_of_typ ctxt'
     #> REPL.trim_makrup
    end

fun string_of_sort ctxt =
    Syntax.string_of_sort ctxt #> REPL.trim_makrup

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

(* All readers feed the agent string(s) as POSITIONED input via Inner_Syntax_Error
   so a parse failure brackets the offending token with 【 】 (see that module).
   The list/typed variants implode each element under a distinct id, keeping the
   single batched read call (joint type inference unchanged).  On a non-position
   error the original exception propagates to the existing release_par_error. *)

fun read_term ctxt s =
  \<^try>\<open>Inner_Syntax_Error.read_positioned Syntax.read_term ctxt s
   catch exn => release_par_error exn\<close>
  |> Minilang.deconflict_bound_names

(* Like read_term, but in mode_abbrev: the checked term keeps non-internal
   abbreviation constants instead of expanding them. *)
fun read_term_abbrev ctxt s =
  \<^try>\<open>Inner_Syntax_Error.read_positioned Proof_Context.read_term_abbrev ctxt s
   catch exn => release_par_error exn\<close>
  |> Minilang.deconflict_bound_names

fun read_terms ctxt ss =
  \<^try>\<open>Inner_Syntax_Error.read_positioned_list Syntax.read_terms ctxt ss
   catch exn => release_par_error exn\<close>
  |> map (Minilang.deconflict_bound_names)

fun read_terms_with_type ctxt ss =
  \<^try>\<open>
    Inner_Syntax_Error.read_positioned_typed
      (fn ctxt' => fn tss =>
         map (fn (typ, raw_tm) =>
           Const ("_type_constraint_", typ --> typ) $ Syntax.parse_term ctxt' raw_tm) tss
         |> Syntax.check_terms ctxt')
      ctxt ss
   catch exn => release_par_error exn\<close>

fun read_prop ctxt s =
  \<^try>\<open>Inner_Syntax_Error.read_positioned Syntax.read_prop ctxt s
   catch exn => release_par_error exn\<close>
  |> Minilang.deconflict_bound_names

fun read_props ctxt ss =
  \<^try>\<open>Inner_Syntax_Error.read_positioned_list Syntax.read_props ctxt ss
   catch exn => release_par_error exn\<close>
  |> map (Minilang.deconflict_bound_names)

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

fun intro_subject_state (s: Minilang.state) : Minilang.state option =
  let val st = Minilang.leading_proof_sequent_of s
   in if Minilang.need_intro st
      then SOME s
      else Minilang.standard_intro_fallback s
  end

fun AUTO_INTRO (counters:counters) (opt_bindings: bindings option)
               (s:Minilang.state)
  : bindings * Minilang.state =
  let
    val st = Minilang.leading_proof_sequent_of s

    (* Extract provided bindings, use empty lists if NONE *)
    val (provided_var_names, provided_prem_names) = the_default ([], []) opt_bindings

    (* Flag: whether to report missing bindings *)
    val report_missing = is_some opt_bindings
  in
    (* Step 1: Check if INTRO is applicable, possibly after one silent
       standard_tac step that exposes an intro-able goal. *)
    case intro_subject_state s of
      NONE =>
      let
        (* No leading ⋀/⟹/∀/⟶ to introduce: nothing is bound. Still emit
           INTRO_BINDINGS so the Python side's invariant (exactly one per
           INTRO op) holds. Provided bindings fall entirely into `missing`,
           filtered the same way as the success path below. *)
        val missing_vars = if report_missing
          then filter (fn {internal_name, external_name, ...} =>
                 external_name <> internal_name) provided_var_names
          else []
        val missing_prems = if report_missing then provided_prem_names else []
        val _ = Minilang.get_reporter () (Minilang.Internal (INTRO_BINDINGS {
          missing = (missing_vars, missing_prems),
          auto_introduced = ([], []),
          final = ([], [])
        }))
        (* Also emit `Goals` so the Python side's unified count-based
           block-opening check in `SubgoalMaker` sees "no new subgoals
           opened" for this no-op Intro.  Use `goals_of'` (not
           `Thm.prems_of`) because the state may be in Minilang's
           protected form with nested `HOL.GOAL` wrappers, where
           `prems_of` would only walk the outer `Pure.imp` chain.  We
           `take 1` — the state is unchanged, so it's semantically one
           "unchanged leading goal", matching `report_goal`. *)
        val _ = Minilang.get_reporter ()
                  (Minilang.Goals (Minilang.goals_of' st |> take 1))
      in (([], []), s) end
    | SOME intro_s =>
      let
        val ctxt = Minilang.context_of intro_s
            |> Config.put Printer.show_markup false
        val st = Minilang.leading_proof_sequent_of intro_s

        (* Step 2: Extract quantified variables and premises from goal *)
        val goal_term = Thm.prop_of st
                    |> Logic.dest_implies |> fst
                    |> Minilang.deconflict_bound_names
        val (vars, prems0, _) = Minilang.strip_meta_and_hol_hhf goal_term

        (* strip_meta_and_hol_hhf leaves dangling Bound indices in prems;
           substitute them with Free variables so that aconv matching against
           provided_prem_names (which contain Free-based internal_terms from
           compute_bindings) works correctly. *)
        val frees = rev (map Free vars)
        val prems = map (fn t => Term.subst_bounds (frees, t)) prems0

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

        (* Step 4: Process premises. Find matching agent-provided binding
           per goal prem; otherwise auto-generate a name via counter. *)
        val prem_counter = #prem_counter counters
        val (prem_names_for_intro, matched_prem_terms) =
          let
            val counter_start = Synchronized.value prem_counter
            val (names_with_flags, final_counter) =
              fold_map (fn prem_term => fn counter_val =>
                case find_first (fn {internal_term, ...} => internal_term aconv prem_term)
                                provided_prem_names of
                  SOME {external_name, ...} =>
                    (* Matched: strip any "(k)" suffix to recover the base. *)
                    let val base = Minilang_Aux.base_name external_name
                     in ((SOME base, SOME prem_term), counter_val)
                    end
                | NONE =>
                    let val name = "premise" ^ string_of_int counter_val
                     in ((SOME name, NONE), counter_val + 1)
                    end
              ) prems counter_start
            val _ = Synchronized.change prem_counter (K final_counter)
            val matched = map_filter snd names_with_flags
           in (map fst names_with_flags, matched)
          end

        (* Step 5: Call INTRO. INTRO's F destructures conj prems when
           INTRO_split_prem_conj is on, and flatten_facts produces
           base(1..N) entries in facts'. *)
        val ((params', facts'), s') =
          Minilang.INTRO Minilang.SINGLE_GOAL NONE
                         minilang_var_names (SOME prem_names_for_intro) intro_s

        (* Step 6: Extract context from the new state *)
        val ctxt' = Minilang.context_of s'

        (* Step 7: Build var_bindings and prem_bindings with pretty printing from new context *)
        val var_bindings_final = map2 (fn {internal_name, external_name, ...} => fn (_, ty) =>
                                         {internal_name = internal_name,
                                          external_name = external_name,
                                          typ_pretty = string_of_type ctxt' ty})
                                       var_bindings params'

        (* Each goal prem may expand to multiple atoms in facts' (flatten_facts
           emits base(1..N) when the prem was destructured). unflatten_facts
           groups contiguous atoms by base name, preserving each atom's flat
           external name. All atoms of one group share the origin prem's term
           as internal_term. grouped_facts is parallel to prems by design
           (one group per goal premise). *)
        val grouped_facts = Minilang_Aux.unflatten_facts facts'
        val prem_bindings_final =
          flat (map2 (fn prem_term => fn (_, atoms) =>
                        map (fn (name, prop) =>
                              {internal_term = prem_term,
                               external_name = name,
                               pretty = string_of_term ctxt' prop}) atoms)
                     prems grouped_facts)

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
                           not (exists (fn u => u aconv internal_term) matched_prem_terms))
                         prem_bindings_final

        (* Step 10: Send INTRO_BINDINGS message with three fields *)
        val _ = Minilang.get_reporter () (Minilang.Internal (INTRO_BINDINGS {
          missing = (missing_vars, missing_prems),
          auto_introduced = (auto_vars, auto_prems),
          final = (var_bindings_final, prem_bindings_final)
        }))

        (* Step 11: Emit `Goals` with the actual subgoal terms Intro
           opened as direct children.  The state stored on the stack is
           in Minilang's protected form — `protect_goals` nests
           successive subgoals inside `HOL.GOAL` wrappers — so
           `Thm.prems_of` would only walk the outer `Pure.imp` chain
           and under-count.  `Minilang.goals_of'` walks through the
           nested GOALs and returns the correct list of terms.  Done at
           AUTO_INTRO (the agent-facing boundary) rather than inside
           INTRO'' to prevent double-emit when INTRO'' is called
           internally by SIMPLIFY / CRUSH / TRANSPARENT_INTRO'. *)
        val _ = Minilang.get_reporter ()
                  (Minilang.Goals (Minilang.goals_of'
                                     (Minilang.leading_proof_sequent_of s')))

        (* Step 12: Return results *)
      in
        ((var_bindings_final, prem_bindings_final), s')
      end
  end

fun AUTO_SPLIT_CONJS (s: Minilang.state) : Minilang.state =
  let val s' = Minilang.SPLIT_CONJS s
      val _ = Minilang.get_reporter ()
                (Minilang.Goals (Minilang.goals_of'
                                   (Minilang.leading_proof_sequent_of s')))
  in s' end

(* Compute bindings for the leading proof goal by binding provided names in order.
   When Minilang.INTRO_split_prem_conj is on (the default for the agent) and a
   prem is conj-shaped, a single provided name expands into multiple entries
   with (prem, SOME k) internal_term and "name(k)" external_name — mirroring
   what AUTO_INTRO will emit. *)
fun compute_bindings (s:Minilang.state)
                     (var_names: string list) (fact_names: string list)
  : bindings =
  case intro_subject_state s of
    NONE => ([], [])
  | SOME intro_s =>
      let
        val ctxt = Minilang.context_of intro_s
                  |> Config.put Printer.show_markup false
        val st = Minilang.leading_proof_sequent_of intro_s

        (* Extract quantified variables and premises from goal *)
        val goal_term = Thm.prop_of st |> Logic.dest_implies |> fst
                     |> Minilang.deconflict_bound_names
        val (vars, prems0, _) = Minilang.strip_meta_and_hol_hhf goal_term

        (* strip_meta_and_hol_hhf strips Abs binders without substituting
           the bound variables, so prems0 may contain dangling Bound indices.
           Replace them with Free variables so that downstream pretty-printing
           (string_of_term) does not crash with fastype_of: Bound.
           vars is outermost-first; Bound 0 is the innermost (last) var. *)
        val frees = rev (map Free vars)
        val prems = map (fn t => Term.subst_bounds (frees, t)) prems0

        (* Check length constraints *)
        val num_vars = length vars
        val num_prems = length prems
        val num_var_names = length var_names
        val num_fact_names = length fact_names

        (* Partial bindings are allowed: the first num_var_names quantifiers
           get the provided names, the rest are auto-named by AUTO_INTRO.
           Over-specification is still rejected. *)
        val _ = if num_var_names > num_vars
                then raise Minilang.OPR_FAIL (Minilang.INVALID_OPR,
                       "Too many variable names: goal has " ^ string_of_int num_vars ^
                       " leading quantifier(s) but " ^ string_of_int num_var_names ^
                       " name(s) were provided")
                else ()

        val _ = if num_fact_names > num_prems
                then raise Minilang.OPR_FAIL (Minilang.INVALID_OPR,
                       "Too many fact names: goal has " ^ string_of_int num_prems ^
                       " premise(s) but " ^ string_of_int num_fact_names ^
                       " name(s) were provided")
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

        (* Bind premises in order: fact_names[j] -> prems[j].
           deep_destruct_term returns [prem_term] when INTRO_split_prem_conj
           is off, or the atom list when on. Each atom becomes one FactBinding
           with external_name "base(k)"; singleton cases become one entry with
           external_name = base. All entries for the same prem share
           internal_term = the original prem term. *)
        val prem_bindings =
          let
            val pairs = ListPair.zip (fact_names, prems)
            fun one (ex_name, prem_term) =
              case Minilang.deep_destruct_term ctxt prem_term of
                [_] => [{internal_term = prem_term,
                         external_name = ex_name,
                         pretty = string_of_term ctxt prem_term}]
              | atoms =>
                  map_index (fn (i, atom) =>
                    {internal_term = prem_term,
                     external_name = ex_name ^ "(" ^ string_of_int (i+1) ^ ")",
                     pretty = string_of_term ctxt atom}) atoms
           in maps one pairs
          end
      in
        (var_bindings, prem_bindings)
      end

(* Check if the leading proof goal needs INTRO (i.e., has quantified variables or premises) *)
fun check_need_intro (s:Minilang.state) : bool =
  let val st = Minilang.leading_proof_sequent_of s
   in Minilang.need_intro st
  end

fun AUTO_SIMPLIFY
    (counters: counters)
    (simp_thms: thm list)
    (targeted_thms: (thm * term list) list)
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

          (* Use fold_map to thread counter through all premises. *)
          val (names, final_counter) = fold_map (fn prem_term => fn counter_val =>
            case find_first (fn {internal_term, ...} => internal_term aconv prem_term)
                            provided_prem_names of
              SOME {external_name, ...} =>
                let val _ = matched_prem_terms_ref := prem_term :: !matched_prem_terms_ref
                    val base = Minilang_Aux.base_name external_name
                in (base, counter_val)
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
    val simplify_timeout = SOME (Time.fromSeconds (Config.get ctxt Pre_Simproc.simplify_timeout_seconds))

    (* Build targeted simprocs from user-selected targets.
       Check for stale targets: if a target term no longer exists in the goal,
       discard that rule and report. *)
    val thy = Proof_Context.theory_of ctxt
    val goal_term = Thm.prop_of (Minilang.leading_proof_sequent_of s)
    val (valid_targeted, stale_targeted) =
      List.partition (fn (_, targets) =>
        forall (fn tgt => Term.exists_subterm (fn t => Term.aconv (t, tgt)) goal_term) targets
      ) targeted_thms
    val targeted_simprocs = Minilang.thms_to_targeted_simprocs ctxt valid_targeted

    val fell_back_targets_stale = not (null stale_targeted)

    (* Detect self-looping user rules among non-targeted simp_thms and partition them *)
    fun thm_loops thm =
      exists (fn meta_eq =>
        Looping_Simp.simp_rule_may_loop
          {only_check_local = false, ignore_cond = false, local_ignore_cond = true,
           schematize_local_frees = false}
          ctxt (Thm.prop_of meta_eq))
      (Raw_Simplifier.mksimps ctxt thm)
    val (looping_thms, safe_thms) = List.partition thm_loops simp_thms
    val has_looping = not (null looping_thms)
    val base_simp_thms = if has_looping then safe_thms else simp_thms

    fun do_simplify thms simprocs use_sys =
      (Minilang.SIMPLIFY_GOAL_AND_PREMISES
        thms (simprocs @ targeted_simprocs) use_sys premise_names simplify_goal
        (SOME naming_prems_fn) (SOME naming_vars_fn) simplify_timeout) s

    fun mk_base_simprocs () =
      if has_looping then Looping_Simp.thms_to_once_simprocs ctxt looping_thms
      else []

    fun mk_all_once () = Looping_Simp.thms_to_once_simprocs ctxt simp_thms

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

        (* Build final premise bindings from facts' returned by SIMPLIFY.
           INTRO' may split conjunction premises (INTRO_split_prem_conj),
           so facts' can have more entries than prems_before_ref.
           Group by base name to restore 1:1 alignment with the original
           premise terms, then flatten the per-atom bindings. *)
        val facts_grouped = Minilang_Aux.unflatten_facts facts'
        val prem_bindings_final =
          map2 (fn prem_term => fn (_, atoms) =>
            map (fn (flat_name, exterm) =>
              {internal_term = prem_term,
               external_name = flat_name,
               pretty = string_of_term ctxt' exterm}) atoms
          ) (!prems_before_ref) facts_grouped
          |> flat

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
    val _ = if fell_back_targets_stale
            then let val stale_names = map (fn (thm, _) =>
                        Thm_Name.print (Thm.get_name_hint thm)
                        handle ERROR _ => "<unnamed>") stale_targeted
                 in Minilang.get_reporter ()
                      (Minilang.Internal (SIMPLIFY_TARGETS_STALE stale_names))
                 end
            else ()
  in
    s'
  end

exception FACT_IN_TIME_FAIL of term

(* Resolve FactInTime: prove the statement, register in context, return FactByName.
   FactByName passes through unchanged. Threads updated context via fold.
   The assigned name comes from the FactInTime tuple (set by Python). *)
fun pre_resolve_fact (FactByName fref) ctxt = (fref, ctxt)
  | pre_resolve_fact (FactInTime (assigned_name, prop)) ctxt =
      let val goal = Goal.init (Thm.cterm_of ctxt prop)
          val proved =
            (case Seq.pull (Phi_Sledgehammer_Solver.fast_mepo_tac (Time.fromSeconds 10) ctxt 1 goal)
               of SOME (st', _) => st'
                | NONE => raise FACT_IN_TIME_FAIL prop)
            handle ERROR _ => raise FACT_IN_TIME_FAIL prop
          val thm = Goal.finish ctxt proved
          val ((_, _), ctxt') = Proof_Context.note_thms ""
                ((Binding.name assigned_name, []), [([thm], [])]) ctxt
      in ((Facts.Named ((assigned_name, Position.none), NONE), []), ctxt') end

fun pre_resolve_facts ctxt facts =
  fold_map pre_resolve_fact facts ctxt

(* Resolve extended facts to a flat thm list (for SIMPLIFY, UNFOLD) *)
fun resolve_to_thms ctxt facts =
  let val (refs, ctxt') = pre_resolve_facts ctxt facts
  in maps (Attrib.eval_thms ctxt' o single) refs
  end

(* Resolve extended facts to fact refs, threading context (for RULE, HAMMER, END, NXT) *)
fun resolve_to_refs ctxt facts = pre_resolve_facts ctxt facts

fun resolve_to_override ctxt facts =
  let val (refs, ctxt') = resolve_to_refs ctxt facts
  in (ctxt', {add = refs, del = [], only = false}) end

(* Resolve extended facts and update Minilang state's context *)
fun with_resolved_refs s facts f =
  let val ctxt = Minilang.context_of s
      val (refs, ctxt') = resolve_to_refs ctxt facts
      val s' = Minilang.map_context (K ctxt') s
  in f s' refs end

fun with_resolved_override s facts f =
  let val ctxt = Minilang.context_of s
      val (ctxt', ovr) = resolve_to_override ctxt facts
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

(* Fold the recorded post-rule instantiation rounds onto the post-rule
   state. Per round: parse each var-name to an indexname, partition into
   type insts (?'a) and term insts (?x) by leading "'", then apply the
   2-phase Minilang.INST_GOAL_VARS primitive (types first, then terms).
   The instantiation VALUE strings are agent-supplied; INST_GOAL_VARS runs on the
   plain strings, and a parse failure is re-probed positioned for a 【 】 marker
   (term values via read_term, type values via read_typ) (M1). *)
fun apply_post_insts rounds state =
  fold (fn round => fn st =>
    let
      val ctxt = Minilang.context_of st
      val parsed = map (fn (name, value) => (Minilang_Aux.parse_var name, value)) round
      val (tinsts, insts) =
        List.partition (fn (idx, _) => Minilang_Aux.is_tvar_name (Minilang_Aux.VN_IndexName idx))
          parsed
      fun reprobe () =
        case Inner_Syntax_Error.marker_strings Syntax.read_term ctxt (map snd insts) of
          SOME m => SOME m
        | NONE => Inner_Syntax_Error.marker_strings Syntax.read_typ ctxt (map snd tinsts)
    in Inner_Syntax_Error.guard reprobe (fn () => Minilang.INST_GOAL_VARS (tinsts, insts) st)
    end)
  rounds state

fun interpret_i (config as (_, _, counters, exec_mode)) cmd s =
  case cmd of
      SIMPLIFY (simp_facts_with_targets, use_system_simps, premise_names, simplify_goal, user_bindings_opt) =>
        let val ctxt = Minilang.context_of s
            (* Split facts into targeted and non-targeted *)
            val (targeted_entries, normal_facts) =
              fold_rev (fn (fact, SOME targets) => apfst (cons (fact, targets))
                         | (fact, NONE) => apsnd (cons fact))
                simp_facts_with_targets ([], [])
            val simp_thms = resolve_to_thms ctxt normal_facts
            val targeted_thms =
              maps (fn (fact, targets) =>
                map (fn thm => (thm, targets))
                    (resolve_to_thms ctxt [fact])
              ) targeted_entries
         in AUTO_SIMPLIFY counters simp_thms targeted_thms use_system_simps premise_names
                          simplify_goal user_bindings_opt s
        end
    | UNFOLD facts =>
        let val _ = if null facts
                    then error "You must specify at least one theorem to unfold"
                    else ()
            val ctxt = Minilang.context_of s
            val defs = resolve_to_thms ctxt facts
        in Minilang.UNFOLD defs s
        end
    | WITNESS terms =>
        Minilang.CHOOSE terms s
    | RULE (facts, insts) =>
        with_resolved_refs s facts (fn s' => fn refs =>
          apply_post_insts insts (Minilang.RULE refs [] s'))
    | CASE_SPLIT (target, vars, rule, no_simp, insts) =>
        apply_post_insts insts
          (Minilang.CASE_SPLIT (no_simp, ([[SOME target]], rule)) vars [] s)
    | INDUCT (target, vars, arbitrary, gen_fact_refs, rule, no_simp, insts) =>
        let val ctxt = Minilang.context_of s
            val vs = map (fn Free nt => nt
                           | x => error ("The `arbitrary` argument must be variables, but (" ^
                                         string_of_term ctxt x ^ ") is given.")) arbitrary
            (* `gen_fact_refs` is the resolved icmd-level fact list
             * (`Facts.ref * Token.src list` — see the datatype at the
             * top of this file), produced by `check_command_i`'s call
             * to `read_fact`. We evaluate each one to thms via the
             * standard `Attrib.eval_thms`, which respects every
             * selector form Parse.thm accepts (`h`, `h(1)`, `h(2-4)`,
             * `h[attr]`) — index-selection is handled inside by
             * `Facts.interval`. `Facts.string_of_ref` round-trips the
             * ref back to the display string, so the binding we hand
             * to `update_tampered` matches what items-channel
             * rendering (via flatten_facts) would show. *)
            val named_insertion =
              map (fn (ref_, _) =>
                    let val name = Facts.string_of_ref ref_
                        val thms = Attrib.eval_thms ctxt [(ref_, [])]
                    in (name, thms) end)
                  gen_fact_refs
        in apply_post_insts insts
             (Minilang.INDUCT
                    (no_simp, ([[SOME (NONE, (target, false))]], (([vs], []), Option.map single rule))) vars
                    {using = [], insertion = named_insertion} s)
        end
    | NEXT_OR_END (lemmas, vars) =>
        with_resolved_override s lemmas (fn s' => fn ovr =>
          Minilang.END_or_NXT vars ovr s')
    | NEXT (lemmas, vars) =>
        with_resolved_override s lemmas (fn s' => fn ovr =>
          Minilang.NXT vars ovr s')
    | END lemmas =>
        with_resolved_override s lemmas (fn s' => fn ovr =>
          Minilang.END ovr s')
    | BRANCH branches =>
        let val brs = map (fn (SOME name, br) =>
                  ([], ([], [], [((Binding.name name, []), [(br, [])])]))
                | (NONE, _) => error "Branch case name is required"
              ) branches
        in Inner_Syntax_Error.guard
             (fn () => Inner_Syntax_Error.marker_strings Syntax.read_prop
                         (Minilang.context_of s) (map snd branches))
             (fn () => Minilang.CONSIDER brs s)
        end
    | HAVE (name, fixes, assumes, conclusion, auto_apply) =>
        let val prem_ctr = #prem_counter counters
            val counter_start = Synchronized.value prem_ctr
            val (named_assumes, final_counter) = fold_map (fn (name_opt, prop) => fn ctr =>
                  let val (nm, ctr') = case name_opt of
                          SOME n => (n, ctr)
                        | NONE => ("premise" ^ string_of_int ctr, ctr + 1)
                  in (((Binding.name nm, []), [(prop, [])]), ctr')
                  end) assumes counter_start
            val _ = Synchronized.change prem_ctr (K final_counter)
            val attr_srcs = if auto_apply
                  then [Token.make_src ("mini_auto_apply", Position.none) []]
                  else []
            val fixes' = map (fn (n, T) => (Binding.name n, T, NoSyn)) fixes
            val shows = [((Binding.name name, attr_srcs), [(conclusion, [])])]
         in Inner_Syntax_Error.guard
              (fn () => Inner_Syntax_Error.marker_strings Syntax.read_prop
                          (Minilang.context_of s) (conclusion :: map snd assumes))
              (fn () => Minilang.HAVE fixes' named_assumes shows s)
        end
    | SUFFICES (fixes, assumes, conclusion) =>
        let val prem_ctr = #prem_counter counters
            val counter_start = Synchronized.value prem_ctr
            val (named_assumes, final_counter) = fold_map (fn (name_opt, prop) => fn ctr =>
                  let val (nm, ctr') = case name_opt of
                          SOME n => (n, ctr)
                        | NONE => ("premise" ^ string_of_int ctr, ctr + 1)
                  in (((Binding.name nm, []), [(prop, [])]), ctr')
                  end) assumes counter_start
            val _ = Synchronized.change prem_ctr (K final_counter)
            val fixes' = map (fn (n, T) => (Binding.name n, T, NoSyn)) fixes
            val shows = [((Binding.empty, []), [(conclusion, [])])]
         in Inner_Syntax_Error.guard
              (fn () => Inner_Syntax_Error.marker_strings Syntax.read_prop
                          (Minilang.context_of s) (conclusion :: map snd assumes))
              (fn () => Minilang.SUFFICES fixes' named_assumes shows s)
        end
    | OBTAIN (vars, constraints) =>
        let val named_constraints = map (fn (SOME name, goal) =>
                  ((Binding.name name, []), [(goal, [])])
                | (NONE, _) => error "Obtain constraint name is required"
              ) constraints
            val arg = [(map (fn (v,T) => (Binding.name v, T, NoSyn)) vars,
                       ([], [], named_constraints))]
        in Inner_Syntax_Error.guard
             (fn () => Inner_Syntax_Error.marker_strings Syntax.read_prop
                         (Minilang.context_of s) (map snd constraints))
             (fn () => Minilang.CONSIDER arg s)
        end
    | SORRY_NEXT vars =>
        Minilang.SORRY_NEXT vars s
    | SORRY_END_ALL vars =>
        Minilang.SORRY_END_ALL vars s
    | SORRY_ONLY =>
        Minilang.SORRY_ONLY s
    | HAMMER (facts, timeout, cached_proof) =>
        let
          val ctxt0 = Minilang.context_of s
          val (ctxt_r, ovr) = resolve_to_override ctxt0 facts
          val s_resolved = Minilang.map_context (K ctxt_r) s

          fun hammer_live () = (
            Timeout.apply (Time.fromSeconds 1200) (fn () =>
              let val improved_SH = Config.get ctxt_r Minilang.mini_use_improved_SH
                  val override' = if improved_SH then ovr
                                  else Sledgehammer_Fact.no_fact_override
                  val prover = fn id => Phi_Sledgehammer_Solver.auto_raw
                                 improved_SH override' id (SOME (Time.fromSeconds timeout))
              in Minilang.HAMMER prover s_resolved
              end) ()
            handle Timeout.TIMEOUT _ =>
              raise Minilang.OPR_FAIL (Minilang.PROOF_FAIL,
                "Automatic proof timed out (20 min). The goal is non-trivial and a step-by-step proof is required.")
                 | Phi_Sledgehammer_Solver.Auto_Fail reason =>
              let val msg = case reason
                    of Phi_Sledgehammer_Solver.Subgoal_Fail sub =>
                         "Automatic proof fails on the subgoal:\n  " ^
                         string_of_term ctxt_r sub ^
                         "\nThe goal is non-trivial and a step-by-step proof is required."
                     | _ => "Automatic proof fails. The goal is non-trivial and a step-by-step proof is required."
              in raise Minilang.OPR_FAIL (Minilang.PROOF_FAIL, msg)
              end
                 | Minilang.OPR_FAIL (Minilang.PROOF_FAIL, _) =>
              raise Minilang.OPR_FAIL (Minilang.PROOF_FAIL,
                "Automatic proof fails. The goal is non-trivial and a step-by-step proof is required."))

          fun try_cached_apply (prf, time_ms) =
            let val replay_timeout = Time.fromMilliseconds
                      (Real.round (1.5 * Real.fromInt time_ms) + 3000)
                val kws = Thy_Header.get_keywords (Proof_Context.theory_of ctxt_r)
                val toks = Input.source_explode (Input.string prf)
                        |> Token.tokenize (Keyword.no_major_keywords kws) {strict = false}
                        |> filter Token.is_proper
                val method_text = case Scan.read Token.stopper (Method.parser 0 >> #1) toks of
                    SOME m => m
                  | NONE => error ("Cannot parse cached method: " ^ quote prf)
                val s' = Minilang.APPLY (SOME replay_timeout) []
                           (Method.check_text ctxt_r method_text) s_resolved
                val _ = Minilang.get_reporter ()
                          (Minilang.Internal (Minilang.SH_PRF (prf, Time.fromMilliseconds time_ms)))
            in s' end

        in case (cached_proof, exec_mode) of
            (SOME (prf, ms), _) =>
              if prf = "" then
                (case exec_mode of
                   LIVE => hammer_live ()
                 | REPLAY => raise Minilang.OPR_FAIL (Minilang.PROOF_FAIL,
                     "Cached proof is empty (classical automation) and replay mode forbids sledgehammer"))
              else
                (\<^try>\<open>try_cached_apply (prf, ms)
                  catch exn => (fn () =>
                   case exec_mode of
                     LIVE => hammer_live ()
                   | REPLAY => raise Minilang.OPR_FAIL (Minilang.PROOF_FAIL,
                       "Cached proof replay failed: " ^ Runtime.exn_message exn)
                   ) ()\<close>)
          | (NONE, LIVE) => hammer_live ()
          | (NONE, REPLAY) =>
              raise Minilang.OPR_FAIL (Minilang.PROOF_FAIL,
                "No cached proof available and replay mode forbids sledgehammer")
        end
    | INTRO opt_bindings =>
        #2 (AUTO_INTRO counters opt_bindings s)
    | SPLIT_CONJS => AUTO_SPLIT_CONJS s
    | SPECIALIZE (name, rule_fact, insts, discharge_facts) =>
        let val ctxt = Minilang.context_of s
            val rule_thms = resolve_to_thms ctxt [rule_fact]
            val discharge_thms = resolve_to_thms ctxt discharge_facts
            val insts' = map (fn (n, tm) =>
              if String.isPrefix "?" n then
                case Lexicon.read_variable n of
                  SOME xi => (Minilang_Aux.VN_IndexName xi, tm)
                | NONE => raise Minilang.OPR_FAIL (Minilang.INVALID_OPR,
                            "Specialize: cannot parse variable name " ^ quote n)
              else (Minilang_Aux.VN_Name n, tm)) insts
            val facts_before = Minilang.get_local_facts s
            val s' = Minilang.SPECIALIZE'' (SOME name) rule_thms (insts', []) discharge_thms s
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
        with_resolved_refs s facts (fn s' => fn refs =>
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
          val decls : (binding * string option * mixfix) list =
            [(Binding.name name, ty_opt, NoSyn)]
          val specs : Specification.multi_specs_cmd =
            map (fn eq => ((Binding.empty_atts, eq), [], [])) equations
          val ctxt0 = Minilang.context_of s
          (* equations + optional type string are agent-supplied; on a parse
             failure re-probe them positioned for a 【 】 marker (M3). *)
          fun reprobe () =
            case Inner_Syntax_Error.marker_strings Syntax.read_prop ctxt0 equations of
              SOME m => SOME m
            | NONE => Inner_Syntax_Error.marker_strings Syntax.read_typ ctxt0 (the_list ty_opt)
          (* A nullary constant (head applied to no arguments, e.g.
             `P = 5`) cannot go through the function/fun package — it
             rejects an argument-free LHS with "Function has no
             arguments". Route such definitions through the plain Isar
             `define` command instead; all other (function-style)
             definitions keep going through FUN'' unchanged.

             The defined head's type is reported back (via DEFINE_RESULT)
             so the Python side can update Define._fixed_vars_at_me /
             _after_me even when the user omitted the type field. The two
             paths obtain it differently and MUST NOT share a fallback:
             import_last_function returns the *last function in the
             ambient context*, which on the define path is some unrelated
             leftover — so the define path reads the freshly-fixed head
             directly instead. *)
          val (s', ty_str) = Inner_Syntax_Error.guard reprobe (fn () =>
            if Minilang.is_nullary_def_cmd decls specs ctxt0
            then
              let
                val defs : (Attrib.binding * (string * string list) list) list =
                  map (fn eq => (Binding.empty_atts, [(eq, [])])) equations
                val s' = Minilang.DEFINE'' decls defs [] s
                val ctxt' = Minilang.context_of s'
                val ty_str =
                  case try (Syntax.read_term ctxt') name of
                    SOME t => string_of_type ctxt' (fastype_of t)
                  | NONE => the_default "?" ty_opt
              in (s', ty_str) end
            else
              let
                val s' = Minilang.FUN'' decls specs
                           {metric = metric, open_on_fail = true} s
                val ctxt' = Minilang.context_of s'
                val ty_str =
                  case Function_Common.import_last_function ctxt' of
                    SOME {fs = f :: _, ...} =>
                      string_of_type ctxt' (fastype_of f)
                  | _ => the_default "?" ty_opt
              in (s', ty_str) end)
          val _ = Minilang.get_reporter ()
                    (Minilang.Internal (DEFINE_RESULT (name, ty_str)))
        in s' end
    | SKIP => s
    | CONTRADICTION hyp_name =>
        let
          val st = Minilang.leading_proof_sequent_of s
          val goal = Logic.strip_imp_concl (Thm.major_prem_of st)
          val is_neg = (case goal of
              Const(\<^const_name>\<open>Trueprop\<close>, _) $
                (Const(\<^const_name>\<open>Not\<close>, _) $ _) => true
            | _ => false)
          val rule_name = if is_neg then "notI" else "ccontr"
          val rule_ref = (Facts.Named ((rule_name, Position.none), NONE), [])
          val s' = Minilang.RULE [rule_ref] [] s
          val ((params', facts'), s'') =
                Minilang.INTRO Minilang.SINGLE_GOAL NONE
                               NONE (SOME [SOME hyp_name]) s'
          val ctxt'' = Minilang.context_of s''
          val var_bindings = map (fn (name, ty) =>
                {internal_name = name, external_name = name,
                 typ_pretty = string_of_type ctxt'' ty}) params'
          val prem_bindings = map (fn (name, prop) =>
                {internal_term = prop, external_name = name,
                 pretty = string_of_term ctxt'' prop}) facts'
          val _ = Minilang.get_reporter ()
                    (Minilang.Internal (INTRO_BINDINGS {
                        missing = ([], []),
                        auto_introduced = ([], []),
                        final = (var_bindings, prem_bindings)
                    }))
        in s'' end
    | SETUP_REWRITING (name, for_any, conditions, redex, residue) =>
        let
          val ctxt = Minilang.context_of s

          (* Prepare and fix for_any variables — follow Specification.prep_decls pattern:
             read_var parses type strings and declares constraints, add_fixes fixes them *)
          val raw_vars = map (fn (n, T) => (Binding.name n, T, NoSyn)) for_any
          val (vars, vars_ctxt) = fold_map Proof_Context.read_var raw_vars ctxt
          val (_, fixes_ctxt) = Proof_Context.add_fixes vars vars_ctxt

          (* Parse ALL terms together for consistent type inference *)
          val cond_strs = map snd conditions
          val (redex_term :: residue_term :: cond_terms_raw) =
                read_terms fixes_ctxt (redex :: residue :: cond_strs)

          (* Wrap boolean conditions in Trueprop; leave prop-typed ones as-is *)
          val cond_terms = map (fn t =>
                case fastype_of t of
                  \<^Type>\<open>bool\<close> => HOLogic.mk_Trueprop t
                | _ => t) cond_terms_raw

          val equation = HOLogic.mk_Trueprop (HOLogic.mk_eq (redex_term, residue_term))

          (* Looping check — before calling HAVE'', from parsed terms directly *)
          val meta_eq_prop = Logic.mk_equals (redex_term, residue_term)
          val may_loop = Looping_Simp.simp_rule_may_loop
                {only_check_local = true, ignore_cond = true, local_ignore_cond = true,
                 schematize_local_frees = false}
                fixes_ctxt meta_eq_prop
          val _ = if may_loop then
                    Minilang.get_reporter ()
                      (Minilang.Internal SETUP_REWRITING_MAY_LOOP)
                  else ()

          (* Build named assumes from parsed conditions *)
          val prem_ctr = #prem_counter counters
          val counter_start = Synchronized.value prem_ctr
          val (named_assumes, final_counter) =
            fold_map (fn ((name_opt, _), cond_term) => fn ctr =>
                let val (nm, ctr') = case name_opt of
                        SOME n => (n, ctr)
                      | NONE => ("premise" ^ string_of_int ctr, ctr + 1)
                in (((Binding.name nm, []), [(cond_term, [])]), ctr')
                end) (conditions ~~ cond_terms) counter_start
          val _ = Synchronized.change prem_ctr (K final_counter)

          val fixes' = vars
          val attr_srcs = [Token.make_src ("Minilang_Agent.mini_auto_apply", Position.none) []]
          val shows = [((Binding.name name, attr_srcs), [(equation, [])])]
          val s' = Minilang.HAVE'' fixes' named_assumes shows s
        in s' end
    | COMPUTE (name, term) =>
        let val facts_before = Minilang.get_local_facts s
            val s' = Minilang.COMPUTE name term s
            val ctxt' = Minilang.context_of s'
            val facts_after = Minilang.get_local_facts s'
            val new_facts = filter (fn (n, _) =>
                  not (exists (fn (n', _) => n = n') facts_before)) facts_after
            val _ = case new_facts of
                  [(rn, rt)] => Minilang.get_reporter ()
                                  (Minilang.Internal (COMPUTE_RESULT (rn, string_of_term ctxt' rt)))
                | _ => ()
        in s' end

local
val keywords = Thy_Header.get_keywords @{theory Pure}

(* Qualified fact names whose first segment is numeric -- e.g. "1.IH"
   from `nat_less_induct`'s `Rule_Cases.extract_case` -- tokenize as
   three separate tokens [Nat "1", ".", Ident "IH"] (scan_longid needs
   both segments to be identifiers), so Parse.thm consumes only "1"
   and leaves ".IH" unconsumed. Fold such <Nat> "." <seg> ("." <seg>)*
   runs into a single Str token so Parse.thm's name-position path
   accepts them, while attribute [...] and selector (...) groups after
   the name remain untouched. *)
fun merge_qualified_nat_names toks =
  let
    fun is_dot t = Token.content_of t = "."
    fun is_name_seg t = member (op =)
          [Token.Ident, Token.Long_Ident, Token.Nat] (Token.kind_of t)
    fun scan (acc, t :: u :: rest) =
          if is_dot t andalso is_name_seg u
          then scan (acc ^ "." ^ Token.content_of u, rest)
          else (acc, t :: u :: rest)
      | scan (acc, rest) = (acc, rest)
    fun walk (t :: u :: rest) =
          if Token.kind_of t = Token.Nat andalso is_dot u
          then
            let val (name, rest') = scan (Token.content_of t, u :: rest)
             in Token.make_string (name, Token.pos_of t) :: walk rest' end
          else t :: walk (u :: rest)
      | walk xs = xs
  in walk toks end

fun read_fact src =
  let val symbols = Input.source_explode (Input.string src)
      val toks = Token.tokenize keywords {strict = true} symbols
              |> filter Token.is_proper
              |> merge_qualified_nat_names
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
  | check_extended_fact ctxt (FactInTime (assigned_name, stmt)) =
      FactInTime (assigned_name, read_prop ctxt stmt)

in

val read_thms = read_thms

fun check_command_i s (SIMPLIFY (facts_with_targets, use_sys, prems, simp_goal, bindings_opt)) =
      let val ctxt = Minilang.context_of s
      in SIMPLIFY (map (fn (fact, targets) => (check_extended_fact ctxt fact, targets)) facts_with_targets,
                   use_sys, prems, simp_goal, bindings_opt) end
  | check_command_i s (RULE (facts, insts)) =
      let val ctxt = Minilang.context_of s
      in RULE (map (check_extended_fact ctxt) facts, insts) (*insts: parsed at interpret time*) end
  | check_command_i s (UNFOLD facts) =
      let val ctxt = Minilang.context_of s
      in UNFOLD (map (check_extended_fact ctxt) facts) end
  | check_command_i s (WITNESS terms) =
      let val ctxt = Minilang.context_of s
          val typs = get_witness_types s
          val num_typs = length typs
          val num_terms = length terms
          (* Allow partial instantiation: witnesses (left-to-right) may be fewer
             than the leading existentials; any un-witnessed suffix is left as a
             residual existential goal for a later Witness step. This gate rejects
             only a non-existential goal and more witnesses than quantifiers;
             num_terms = 0 is a harmless no-op here (the empty list is rejected
             upstream by the Python Witness validator). *)
          val _ = if num_typs = 0 then
                    raise Minilang.OPR_FAIL (Minilang.INVALID_OPR,
                      "The proof goal is not led by an existential quantification")
                  else if num_terms > num_typs then
                    raise Minilang.OPR_FAIL (Minilang.INVALID_OPR, String.concat [
                      "Too many witness terms: the goal has ",
                      string_of_int num_typs,
                      " leading existential quantifier",
                      if num_typs = 1 then "" else "s",
                      " but ",
                      string_of_int num_terms,
                      " were provided"
                    ])
                  else ()
          val typed_terms = ListPair.zip (typs, terms)
       in WITNESS (read_terms_with_type ctxt typed_terms)
      end
  | check_command_i s (CASE_SPLIT (target, vars, rule, no_simp, insts)) =
      let val ctxt = Minilang.context_of s
          val rule' = Option.map (chk_single ctxt rule o read_thms ctxt) rule
          val target' = read_term ctxt target
       in CASE_SPLIT (target', vars, rule', no_simp, insts) (*insts: parsed at interpret time*)
      end
  | check_command_i s (INDUCT (target, vars, arbitrary, gen_fact_names, rule, no_simp, insts)) =
      let val ctxt = Minilang.context_of s
          val (target' :: arbitrary') = read_terms ctxt (target :: arbitrary)
          val rule' = Option.map (chk_single ctxt rule o read_thms ctxt) rule
          (* Parse each facts_to_generalize name string into a
           * Facts.ref (via the standard Parse.thm path). Supports
           * `h`, `h(i)`, `h(i-j)`, `h[attr]`. Defensive "local."
           * strip matches items-channel naming. *)
          val gen_fact_refs =
            map (read_fact o Minilang_Aux.simp_fact_name') gen_fact_names
       in INDUCT (target', vars, arbitrary', gen_fact_refs, rule', no_simp, insts) (*insts: parsed at interpret time*)
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
  | check_command_i _ (HAVE data) = HAVE data
  | check_command_i _ (SUFFICES data) = SUFFICES data
  | check_command_i _ (OBTAIN vc) = OBTAIN vc (*name_opt * string passthrough*)
  | check_command_i _ (SORRY_NEXT vars) = SORRY_NEXT vars
  | check_command_i _ (SORRY_END_ALL vars) = SORRY_END_ALL vars
  | check_command_i _ SORRY_ONLY = SORRY_ONLY
  | check_command_i s (HAMMER (facts, timeout, cached_proof)) =
      let val ctxt = Minilang.context_of s
      in HAMMER (map (check_extended_fact ctxt) facts, timeout, cached_proof) end
  | check_command_i _ (INTRO opt_bindings) = INTRO opt_bindings
  | check_command_i _ SPLIT_CONJS = SPLIT_CONJS
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
  | check_command_i _ (CONTRADICTION hyp) = CONTRADICTION hyp
  | check_command_i _ (SETUP_REWRITING data) = SETUP_REWRITING data
  | check_command_i s (COMPUTE (name, raw_term)) =
      let val ctxt = Minilang.context_of s
          val term = read_term ctxt raw_term
          (* Enumerate exactly which atoms make the term non-ground, so the
             agent can spot e.g. a free variable that merely *looks* like a
             type (an induction case var named `nat` reads as `nat :: nat`). *)
          val _ =
            if Ground_Eval.is_ground term then ()
            else
              let
                fun bullet line = "\n  - " ^ line
                val free_lines =
                  map (fn (n, T) =>
                        bullet ("free variable: "
                                ^ string_of_term ctxt (Free (n, T))
                                ^ " :: " ^ string_of_type ctxt T))
                      (Term.add_frees term [])
                val var_lines =
                  map (fn (ni, T) =>
                        bullet ("schematic variable: "
                                ^ string_of_term ctxt (Var (ni, T))
                                ^ " :: " ^ string_of_type ctxt T))
                      (Term.add_vars term [])
                val tfree_lines =
                  map (fn (n, S) =>
                        bullet ("free type variable: "
                                ^ string_of_type ctxt (TFree (n, S))))
                      (Term.add_tfrees term [])
                val tvar_lines =
                  map (fn (ni, S) =>
                        bullet ("schematic type variable: "
                                ^ string_of_type ctxt (TVar (ni, S))))
                      (Term.add_tvars term [])
              in raise Minilang.OPR_FAIL (Minilang.INVALID_OPR,
                   String.concat (
                     ["Compute requires a fully concrete ground term, but `",
                      string_of_term ctxt term,
                      "` contains the following free or schematic variables:"]
                     @ free_lines @ var_lines @ tfree_lines @ tvar_lines))
              end
      in COMPUTE (name, term)
      end

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
