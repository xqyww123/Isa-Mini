(*TODO: name anounymous hyps ""*)

signature MINILANG_AGENT_AoA = sig

type driver = string
val default_driver: driver
val agent_aoa_driver: string Config.T
val AoA_log_dir: string Config.T
val AoA_interactive_retrieval: string Config.T
val AoA_retrieval_forking: string Config.T

type state_id = string
type states = Minilang.state Symtab.table

val AoA_RPC : driver * (MiniLang_Agent.cfg * MiniLang_Agent.budget) * string
           -> Proof.context * thm
           -> MiniLang_Agent.xcmd list * thm (*acomplished proof sequent*)

val method : thm list -> context_state -> context_state Seq.result Seq.seq

(* Query entity by kind and name via the AoA query tool's Python core.
   Returns (formatted_text, is_error). *)
val query_by_name : Context.generic ->
  Universal_Key.entity_kind * string -> string * bool

end

structure MiniLang_Agent_AoA : MINILANG_AGENT_AoA = struct

type driver = string
val default_driver = "ClaudeCode"

(* Config for driver selection *)
val agent_aoa_driver = Attrib.setup_config_string \<^binding>\<open>agent_AoA_driver\<close> (K default_driver)

type state_id = string
type states = Minilang.state Symtab.table
type cfg = MiniLang_Agent.cfg * MiniLang_Agent.budget

type context = {
    vars: (string * typ) list,
    hyps: (string * term) list
  }
type goal = {context: context, goal: term}
type goals = {context: context, goals: goal list}

fun chk_initial_state (states:states) =
  if Symtab.size states = 1
  then case Symtab.lookup states "$init"
    of SOME state => state
     | NONE => error "Not an initial state"
  else error "Not an initial state"

fun general_vars_of (Abs (name,typ,X)) rets = general_vars_of X (insert (op =) (name,typ) rets)
  | general_vars_of (A $ B) rets = general_vars_of B (general_vars_of A rets)
  | general_vars_of (Free (name,typ)) rets = insert (op =) (name,typ) rets
  | general_vars_of (Var ((name,0),typ)) rets = insert (op =) (name,typ) rets
  | general_vars_of (Var ((name,i),typ)) rets = insert (op =) (name^"."^string_of_int i,typ) rets
  | general_vars_of _ rets = rets

(*
fun goals_of_term (seen_vars:(string * typ) list) (hhf:term) : goal =
      let val (vs,hs,cl) = Minilang.strip_meta_and_hol_hhf hhf
       in {context = {vars = filter_out (member (op =) seen_vars) vs,
                      hyps = map (pair "" o single) hs},
           goal=cl}
      end
*)

fun global_context_of (ctxt, goal_sequent) : context =
  let val flattened_hyps = Facts.dest_static false
                            [(Proof_Context.facts_of (Local_Theory.target_of ctxt))]
                            (Proof_Context.facts_of ctxt)
                     |> filter (fn ("local.this", _) => false | _ => true)
                     |> map (apsnd (map Thm.prop_of))
                     |> Minilang_Aux.flatten_facts
                     |> Minilang_Aux.filter_redundant_facts
      val vs = Term.add_frees (Thm.prop_of goal_sequent) []
   in {vars=vs, hyps=flattened_hyps}
  end

local open Find_Theorems in
fun map_criterion _ (Name s) = Name s
  | map_criterion _ Intro = Intro
  | map_criterion _ Elim = Elim
  | map_criterion _ Dest = Dest
  | map_criterion _ Solves = Solves
  | map_criterion F (Simp term) = Simp (F term)
  | map_criterion F (Pattern pat) = Pattern (F pat)
fun check_criterion ctxt =
  let val ctxt' = Proof_Context.set_mode Proof_Context.mode_pattern ctxt
   in map_criterion (MiniLang_Agent.read_term ctxt')
  end
fun uncheck_criterion ctxt = map_criterion (MiniLang_Agent.string_of_term ctxt)
end

local open MessagePackBinIO.Pack MessagePackBinIO.Unpack Remote_Procedure_Calling
in

fun context_packer ctxt =
  let val SOT  = MiniLang_Agent.string_of_term ctxt
      val SOTT = MiniLang_Agent.string_of_type ctxt
   in fn {vars, hyps}:context =>
        packPair (packPairList (packString, packString o SOTT),
                  packPairList (packString, packString o SOT))
                 (vars, hyps)
  end

fun goal_packer ctxt =
  let val SOT  = MiniLang_Agent.string_of_term ctxt
      val context_packer = context_packer ctxt
   in fn {context,goal}:goal =>
        packPair (context_packer, packString o SOT) (context,goal)
  end

local open Find_Theorems in
fun pack_criterion (Name s) = packPair (packInt, packString) (0, s)
  | pack_criterion Intro  = packPair (packInt, packUnit) (1, ())
  | pack_criterion Elim   = packPair (packInt, packUnit) (2, ())
  | pack_criterion Dest   = packPair (packInt, packUnit) (3, ())
  | pack_criterion Solves = packPair (packInt, packUnit) (4, ())
  | pack_criterion (Simp term)   = packPair (packInt, packString) (5, term)
  | pack_criterion (Pattern pat) = packPair (packInt, packString) (6, pat)
val unpack_criterion =
  unpackPair_dep' unpackInt (
    fn 0 => unpackString #> apfst Name
     | 1 => unpackUnit   #> apfst (K Intro)
     | 2 => unpackUnit   #> apfst (K Elim)
     | 3 => unpackUnit   #> apfst (K Dest)
     | 4 => unpackUnit   #> apfst (K Solves)
     | 5 => unpackString #> apfst Simp
     | 6 => unpackString #> apfst Pattern
     | _ => raise Unpack
  )
end

fun minilang_items_packer ctxt =
      context_packer ctxt o (fn (items:Minilang.items) =>
        let val (vars, local_facts) = items
            (* local_facts is already flattened as (string * term) list *)
         in {vars = vars, hyps = local_facts}
        end)
fun minilang_tree_packer ctxt =
  let val term_packer = packString o MiniLang_Agent.string_of_term ctxt
      val item_packer = minilang_items_packer ctxt
      fun pack (Minilang.PROP (items, goal)) =
            packPair (packInt, packPair (item_packer, term_packer)) (0, (items, goal))
        | pack (Minilang.BUNDL (items, trees)) =
            packPair (packInt, packPair (item_packer, packList pack)) (1, (items, trees))
        | pack (Minilang.BLOCK tree) =
            packPair (packInt, pack) (2, tree)
   in pack
  end

fun minilang_message_packer ctxt =
  let val minilang_items_packer = minilang_items_packer ctxt
      val string_of_term = MiniLang_Agent.string_of_term ctxt
      val string_of_type = MiniLang_Agent.string_of_type ctxt
      fun pack (Minilang.New_Items items) =
            packPair (packInt, minilang_items_packer) (0, items)
        | pack (Minilang.Goals goals) =
            packPair (packInt, packList packString)
                     (1, map string_of_term goals)
        | pack (Minilang.Consider_Case (kase, items)) =
            packPair (packInt, packPair (packString, minilang_items_packer)) (2, (kase, items))
        | pack (Minilang.Newly_Fixed vars) =
            packPair (packInt, packList (packPair (packString, packString)))
                     (6, map (apsnd string_of_type) vars)
        | pack (Minilang.Internal exn) =
            (case exn of
               MiniLang_Agent.INTRO_BINDINGS {missing, auto_introduced, final} =>
                 packPair (packInt, packTuple3 (
                   MiniLang_Agent.pack_bindings,
                   MiniLang_Agent.pack_bindings,
                   MiniLang_Agent.pack_bindings
                 )) (3, (missing, auto_introduced, final))
             | MiniLang_Agent.SIMPLIFY_FALLBACK_NOSYS =>
                 packInt 4
             | MiniLang_Agent.SIMPLIFY_FALLBACK_ONCE_SIMPROC =>
                 packInt 9
             | MiniLang_Agent.SIMPLIFY_TARGETS_STALE names =>
                 packPair (packInt, packList packString) (11, names)
             (* (fact_name, pretty_printed_proposition) list *)
             | MiniLang_Agent.SPECIALIZE_RESULT result_facts =>
                 packPair (packInt, packList (packPair (packString, packString)))
                          (5, result_facts)
             | Minilang.PAT_COMPLETENESS_PROOF_OPENED => packInt 7
             | Minilang.TERMINATION_PROOF_OPENED => packInt 8
             | MiniLang_Agent.DEFINE_RESULT (name, ty) =>
                 packPair (packInt, packPair (packString, packString))
                          (10, (name, ty))
             | _ => error "BUG #adli: unexpected Internal message")
   in packList pack o filter (fn Minilang.Internal (MiniLang_Agent.INTRO_BINDINGS _) => true
                                 | Minilang.Internal MiniLang_Agent.SIMPLIFY_FALLBACK_NOSYS => true
                                 | Minilang.Internal MiniLang_Agent.SIMPLIFY_FALLBACK_ONCE_SIMPROC => true
                                 | Minilang.Internal (MiniLang_Agent.SIMPLIFY_TARGETS_STALE _) => true
                                 | Minilang.Internal (MiniLang_Agent.SPECIALIZE_RESULT _) => true
                                 | Minilang.Internal Minilang.PAT_COMPLETENESS_PROOF_OPENED => true
                                 | Minilang.Internal Minilang.TERMINATION_PROOF_OPENED => true
                                 | Minilang.Internal (MiniLang_Agent.DEFINE_RESULT _) => true
                                 | Minilang.Internal _ => false
                                 | _ => true)
  end

local open Facts Minilang_Helper in
fun interval_to_string (FromTo (i,j)) = [string_of_int i, "-", string_of_int j]
  | interval_to_string (From i) = [string_of_int i, "-"]
  | interval_to_string (Single i) = [string_of_int i]
fun intervals_to_string ivs = "(" :: implode_with "," (map interval_to_string ivs) @ [")"]
fun FactRef_to_string (Named ((name, _), NONE)) = name
  | FactRef_to_string (Named ((name, _), SOME [])) = name
  | FactRef_to_string (Named ((name, _), SOME ivs)) = String.concat (name :: intervals_to_string ivs)
  | FactRef_to_string (Fact s) = String.concat ["\<open>", REPL.trim_makrup s, "\<close>"]
val pack_FactRef = packString o FactRef_to_string
end

val AoA_log_dir = Attrib.setup_config_string \<^binding>\<open>AoA_log_dir\<close>
      (fn _ =>
        let val user_home = getenv "ISABELLE_HOME_USER"
        in if user_home = "" then ""
           else user_home ^ "/log/AoA"
        end);

(* Interactive retrieval mode:
   "no"             — direct results, no forking
   "yes"            — fork-based interaction, fork can only answer
   "yes_recursive"  — fork-based interaction, fork can also search (default) *)
val AoA_interactive_retrieval = Attrib.setup_config_string \<^binding>\<open>AoA_interactive_retrieval\<close>
      (K "no");
val _ = Config.register_rpc_option "AoA_interactive_retrieval"
          (Config.string_value AoA_interactive_retrieval);

(* Forking mode for retrieval interactions:
   "with_ctxt" (default)       — fork with opus, inheriting parent context
   "without_ctxt"              — fork with opus, no context inheritance
   "cheaper_no_ctxt"           — fork with sonnet, no context inheritance *)
val AoA_retrieval_forking = Attrib.setup_config_string \<^binding>\<open>AoA_retrieval_forking\<close>
      (K "with_ctxt");
val _ = Config.register_rpc_option "AoA_retrieval_forking"
          (Config.string_value AoA_retrieval_forking);

fun make_invocation_id () =
  let val ms = Time.toMilliseconds (Time.now ())
      val ser = serial ()
      val hex_ms = Int.fmt StringCvt.HEX ms
      val hex_ser = Int.fmt StringCvt.HEX ser
      val hex_ms_last9 = String.substring (hex_ms, Int.max (0, String.size hex_ms - 9), Int.min (9, String.size hex_ms))
   in String.concat [hex_ms_last9, "_", hex_ser]
  end

end

fun AoA_RPC (driver, cfg:cfg, invocation_id) (ctxt0, sequent) =
  let open MessagePackBinIO.Pack MessagePackBinIO.Unpack Remote_Procedure_Calling

      (* Shared state for all callbacks *)
      val counters = {
        prem_counter = Synchronized.var "prem_counter" 0,
        fact_counter = Synchronized.var "fact_counter" 0
      } : MiniLang_Agent.counters
      val messages = Unsynchronized.ref []
      fun listen_report msg = messages := msg :: !messages
      fun clean_report () =
        let val ret = rev (!messages)
         in messages := []; ret end

      (* Configure context *)
      val ctxt = ctxt0
            |> Config.put Minilang.strict_end true
            |> Config.put Minilang.counter_mode "none"
            |> Config.put Minilang.INTRO_split_conj true
            |> Config.put Minilang.INTRO_mk_block true
            |> Config.put Minilang.auto_deconflict_bound true
            |> Config.put Minilang.high_auto_mode true
            |> Config.put Minilang.auto_calculation false
            |> Config.put Printer.show_markup false

      val global_context = global_context_of (ctxt, sequent)
      val s0 = Minilang.INIT ctxt sequent
      val state = Unsynchronized.ref (Symtab.make [("$init", s0)])

      (* Helper: Get state from table *)
      fun get_state state_id =
        case Symtab.lookup (!state) state_id of
          SOME s => s
        | NONE => error "beginning_state_not_found"

      (* Local callback definitions - all share state, counters, messages via closure *)

      val proof_opr_callback = {
        name = "IsaMini.proof_opr",
        arg_schema = unpackTuple3 (unpackString, unpackString, MiniLang_Agent.xcmd_unpacker),
        ret_schema = (fn (ctxt, msgs, tree) =>
          packPair (minilang_message_packer ctxt, minilang_tree_packer ctxt) (msgs, tree)),
        function = (fn (from, to, opr) =>
          let val _ = Minilang.set_reporter listen_report
              val s0 = get_state from
              val (cfg', budget) = cfg
              val full_config = (cfg', budget, counters) : MiniLang_Agent.config
              val s1 = MiniLang_Agent.interpret full_config opr s0
              val ctxt' = Minilang.context_of s1
              val msgs = clean_report ()
              val _ = state := Symtab.update (to, s1) (!state)
           in (ctxt', msgs, Minilang.print_state s1)
          end handle Minilang.OPR_FAIL (Minilang.PROOF_FAIL, msg) =>
              error (REPL.trim_makrup msg)
            | Minilang.OPR_FAIL (Minilang.INVALID_OPR, msg) =>
              error (REPL.trim_makrup msg)
            | Minilang.OPR_FAIL (Minilang.TERMLANG, msg) =>
              error (String.concat ["Syntax Error in Term Language.\n", REPL.trim_makrup msg])
            | MiniLang_Agent.FACT_IN_TIME_FAIL prop =>
              error (String.concat [
                "The following indicated fact is non-trivial, you must prove it manually:\n",
                REPL.trim_makrup (MiniLang_Agent.string_of_term (Minilang.context_of s0) prop)])
            | Phi_Sledgehammer_Solver.Auto_Fail _ =>
              error "Proof operation failed."
            | ERROR msg => error (REPL.trim_makrup msg)),
        timeout = NONE
      }

      val reset_state_callback = {
        name = "IsaMini.reset_state",
        arg_schema = unpackString,
        ret_schema = packUnit,
        function = (fn state_id =>
          (state := Symtab.delete_safe state_id (!state); ())),
        timeout = NONE
      }

      val lookup_fact_callback = {
        name = "IsaMini.lookup_fact",
        arg_schema = unpackPair (unpackString, unpackList (unpackList (unpackPair (unpackBool, unpack_criterion)))),
        ret_schema = (fn (ctxt, rets) =>
          let val SOT = MiniLang_Agent.string_of_term ctxt
           in packList (packPair (pack_FactRef, packString o SOT o Thm.prop_of)) rets
          end),
        function = (fn (state_id, criterions) =>
          let val s0 = get_state state_id
              val ctxt = Minilang.context_of s0
              val check_criterion = check_criterion ctxt
              val rets =
                  maps (fn criterion =>
                        Find_Theorems.find_theorems ctxt
                            (SOME (Minilang.leading_proof_sequent_of s0))
                            (SOME 31) false
                            (map (apsnd check_criterion) criterion)
                     |> snd) criterions
               |> distinct (Thm.equiv_thm (Proof_Context.theory_of ctxt) o apply2 snd)
           in (ctxt, rets)
          end),
        timeout = SOME (Time.fromSeconds 30)
      }

      (* Pre-compute system rule membership tables from the init-time context (ctxt).
         These reflect the background theory's simp/intro/elim declarations, NOT any
         local additions made during the proof (e.g. local simp adds, using-facts).
         TODO: to track proof-local rule changes, the tables would need to be
         rebuilt per proof state from Minilang.context_of. *)
      val simp_rule_names : Strhashtab.set =
        Strhashtab.make_set (map fst (#simps (dest_ss (simpset_of ctxt))))
      (* For intro/elim, Thm.get_name_hint is unreliable (classical_rule derivation
         strips hints). Use iNet keyed by proposition for fast candidate retrieval,
         then post-filter with aconv for exactness. *)
      val (intro_rule_net : term iNet.net, elim_rule_net : term iNet.net) =
        let val cs = Classical.rep_cs (Classical.claset_of ctxt)
            fun build_net items =
              fold (fn (thm, _, _) =>
                let val p = Thm.prop_of thm
                in iNet.insert_term_safe (op aconv) (p, p) end) items iNet.empty
        in (build_net (Item_Net.content (#safeIs cs) @ Item_Net.content (#unsafeIs cs)),
            build_net (Item_Net.content (#safeEs cs) @ Item_Net.content (#unsafeEs cs)))
        end
      fun in_rule_net net prop =
        exists (fn stored => prop aconv stored) (iNet.match_term net prop)
      fun thm_roles thms =
        let val names = map Thm.get_name_hint thms
            val props = map Thm.prop_of thms
        in (if exists (Strhashtab.defined simp_rule_names) names then ["simp"] else []) @
           (if exists (in_rule_net intro_rule_net) props then ["intro"] else []) @
           (if exists (in_rule_net elim_rule_net) props then ["elim"] else [])
        end

      fun abbreviations_in_term ctxt consts term =
        let val contracted = singleton (Syntax.uncheck_terms ctxt) term
        in Term.fold_aterms (fn Const (name, _) =>
              (fn acc =>
                if is_some (try (Consts.the_abbreviation consts) name)
                then insert (op =) name acc
                else acc)
            | _ => I) contracted []
        end

      val retrieve_entity_callback = {
        name = "IsaMini.retrieve_entity",
        arg_schema = unpackPair (unpackString,
          unpackList (unpackPair (Universal_Key.unpack_entity_kind, unpackString))),
        ret_schema = packList (packOption (packTuple4 (packString, packList packString, packList packString, packList packString))),
        function = (fn (state_id, entities) =>
          let val s0 = get_state state_id
              val ctxt = Minilang.context_of s0
              val thy = Proof_Context.theory_of ctxt
              val SOT = MiniLang_Agent.string_of_term ctxt
              val SOTy = MiniLang_Agent.string_of_type ctxt
              val facts = Proof_Context.facts_of ctxt
              val const_space = Proof_Context.const_space ctxt
              val consts = Proof_Context.consts_of ctxt
              val type_space = Proof_Context.type_space ctxt
              val class_space = Proof_Context.class_space ctxt
              val locale_space = Locale.locale_space thy
              fun select_thms thms idx_opt = case idx_opt of
                    NONE => thms
                  | SOME i => if i >= 1 andalso i <= length thms
                              then [nth thms (i - 1)]
                              else []
              fun retrieve_thm name =
                let val (base_name, idx_opt) = Theory_Structure.parse_thm_name name
                    val full_name = Facts.intern facts base_name
                in case Facts.lookup (Context.Proof ctxt) facts full_name of
                     SOME {thms, ...} =>
                       let val thms' = select_thms thms idx_opt
                           val base_extern = Facts.extern ctxt facts full_name
                           val short_name = case idx_opt of
                                 SOME i => Thm_Name.print (base_extern, i)
                               | NONE => base_extern
                           val abbrevs = distinct (op =) (maps
                                (abbreviations_in_term ctxt consts
                                  o Thm.prop_of o Thm.transfer thy) thms')
                       in if null thms' then NONE
                          else SOME (short_name,
                                     map (SOT o Thm.prop_of o Thm.transfer thy) thms',
                                     thm_roles thms',
                                     abbrevs)
                       end
                   | NONE => NONE
                end
              fun retrieve (Universal_Key.TheoremK, name) = retrieve_thm name
                | retrieve (Universal_Key.IntroductionRuleK, name) = retrieve_thm name
                | retrieve (Universal_Key.EliminationRuleK, name) = retrieve_thm name
                | retrieve (Universal_Key.ConstantK, name) =
                    let val name = Consts.intern consts name
                        val short = Name_Space.extern ctxt const_space name
                        val T = Consts.the_constraint consts name
                        val abbrevs = if is_some (try (Consts.the_abbreviation consts) name)
                                      then [name] else []
                    in SOME (short, [SOTy T], [], abbrevs) end
                | retrieve (Universal_Key.TypeK, name) =
                    SOME (Name_Space.extern ctxt type_space name, [], [], [])
                | retrieve (Universal_Key.ClassK, name) =
                    SOME (Name_Space.extern ctxt class_space name, [], [], [])
                | retrieve (Universal_Key.LocaleK, name) =
                    SOME (Name_Space.extern ctxt locale_space name, [], [], [])
          in map (fn e => retrieve e handle ERROR _ => NONE | TYPE _ => NONE) entities end),
        timeout = NONE
      }

      val compute_bindings_callback = {
        name = "IsaMini.compute_bindings",
        arg_schema = unpackTuple3 (unpackString, unpackList unpackString, unpackList unpackString),
        ret_schema = MiniLang_Agent.pack_bindings,
        function = (fn (state_id, var_names, fact_names) =>
          let val s0 = get_state state_id
           in MiniLang_Agent.compute_bindings s0 var_names fact_names
          end handle Minilang.OPR_FAIL (Minilang.INVALID_OPR, msg) =>
              error (String.concat ["Bad operation: ", REPL.trim_makrup msg])),
        timeout = NONE
      }

      val need_intro_callback = {
        name = "IsaMini.need_intro",
        arg_schema = unpackPair (unpackString, unpackBool),
        ret_schema = packBool,
        function = (fn (state_id, consider_conj) =>
          let val s0 = get_state state_id
           in MiniLang_Agent.check_need_intro consider_conj s0
          end),
        timeout = NONE
      }

      val check_term_callback = {
        name = "IsaMini.check_term",
        arg_schema = unpackPair (unpackString, unpackString),
        ret_schema = packTuple3 (packString,
                                 packList (packPair (packString, packString)),
                                 packList (packPair (packString, packString))),
        function = (fn (state_id, term) =>
          let val s0 = get_state state_id
              val ctxt = Minilang.context_of s0
              val string_of_type = MiniLang_Agent.string_of_type ctxt
              val parsed_term = MiniLang_Agent.read_term ctxt term
              val term_type = Term.type_of parsed_term
              val type_string = string_of_type term_type
              val frees = Term.add_frees parsed_term []
                  |> map (fn (name, ty) => (name, string_of_type ty))
              val vars = Term.add_vars parsed_term []
                  |> map (fn (name_idx, ty) =>
                          (Term.string_of_vname name_idx, string_of_type ty))
           in (type_string, frees, vars)
          end handle ERROR msg => error (String.concat ["Unparsed: ", msg])
            | TERM (msg, _) => error (String.concat ["Unparsed: ", msg])
            | TYPE (msg, _, _) => error (String.concat ["Unparsed: ", msg])),
        timeout = NONE
      }

      val schematic_vars_callback = {
        name = "IsaMini.schematic_variables_of",
        arg_schema = unpackString,
        ret_schema = packList (packPair (packString, packString)),
        function = (fn state_id =>
          let val s0 = get_state state_id
              val vars = Minilang.schematic_vars_of_leading_goal s0
              val ctxt = Minilang.context_of s0
              val string_of_type = MiniLang_Agent.string_of_type ctxt
           in map (fn (name_idx, ty) =>
                    (Term.string_of_vname name_idx, string_of_type ty))
                  vars
          end handle ERROR msg => error (String.concat ["Error: ", msg])),
        timeout = NONE
      }

      val potential_defs_callback = {
        name = "IsaMini.potential_defs_of",
        arg_schema = unpackPair (unpackString, unpackList unpackString),
        ret_schema = packList (packTuple3 (packString, packString, packString)),
        function = (fn (state_id, terms) =>
          let val s0 = get_state state_id
              val ctxt = Minilang.context_of s0
              val SOT = MiniLang_Agent.string_of_term ctxt
              val facts = Proof_Context.facts_of ctxt
              val results = List.concat (map (fn term =>
                let val parsed_term = MiniLang_Agent.read_term ctxt term
                    val const_name = case Term.head_of parsed_term of
                                       Const (name, _) => name
                                     | _ => error "term_head_not_const"
                    val defs = Minilang.potential_defs_of_const ctxt const_name
                 in map (fn (name, thm) =>
                      (name, Facts.extern ctxt facts name, SOT (Thm.prop_of thm))) defs
                end) terms)
              val (_, deduped) = fold (fn (triple as (_, _, prop)) => fn (seen, acc) =>
                if member (op =) seen prop then (seen, acc)
                else (prop :: seen, acc @ [triple])) results ([], [])
           in deduped
          end handle ERROR msg => error (String.concat ["Error: ", msg])
            | TERM (msg, _) => error (String.concat ["Error: ", msg])
            | TYPE (msg, _, _) => error (String.concat ["Error: ", msg])),
        timeout = NONE
      }

      val abbreviation_defs_callback = {
        name = "IsaMini.abbreviation_defs",
        arg_schema = unpackPair (unpackString, unpackList unpackString),
        ret_schema = packList (packOption (packPair (packString, packString))),
        function = (fn (state_id, const_names) =>
          let val s0 = get_state state_id
              val ctxt = Minilang.context_of s0
              val consts = Proof_Context.consts_of ctxt
              val ctxt' = Config.put Proof_Context.show_abbrevs false ctxt
              val SOT = MiniLang_Agent.string_of_term ctxt'
          in map (fn name =>
              (let val (T, rhs) = Consts.the_abbreviation consts name
                   val (params, body) = Term.strip_abs rhs
                   val frees = map Free params
                   val body' = Term.subst_bounds (rev frees, body)
                   val lhs = Term.list_comb (Const (name, T), frees)
               in SOME (SOT lhs, SOT body') end)
              handle TYPE _ => NONE
                   | ERROR _ => NONE
                   | TERM _ => NONE)
             const_names
          end),
        timeout = NONE
      }

      val validate_prove_in_time_callback = {
        name = "IsaMini.validate_prove_in_time",
        arg_schema = unpackPair (unpackString, unpackList unpackString),
        ret_schema = packList (packOption packString),
        function = (fn (state_id, stmts) =>
          let val s0 = get_state state_id
              val ctxt = Minilang.context_of s0
          in map (fn stmt => \<^try>\<open>
               let val prop = MiniLang_Agent.read_prop ctxt stmt
                   val goal = Goal.init (Thm.cterm_of ctxt prop)
               in case Seq.pull (Phi_Sledgehammer_Solver.fast_mepo_tac (Time.fromSeconds 3) ctxt 1 goal)
                    of SOME _ => NONE
                     | NONE => SOME "Proof failed"
               end
               catch ERROR msg => SOME (REPL.trim_makrup msg)
                   | Timeout.TIMEOUT _ => SOME "Timed out"
                   | exn => SOME (REPL.trim_makrup (Runtime.exn_message exn))\<close>
            ) stmts
          end),
        timeout = NONE
      }

      val thm_cache = Universal_Key.new_thm_uk_cache ()

      val contextual_thms_callback = {
        name = "IsaMini.contextual_thms",
        arg_schema = unpackString,
        ret_schema = packList (packPair (Universal_Key.pack_universal_key, packString)),
        function = (fn state_id =>
          let val s = get_state state_id
              val context = Context.Proof (Minilang.context_of s)
              val tree = Minilang.print_state s
              val ((_, facts), _) = Minilang.context_of_leading_goal tree
              val names = map fst facts
              val entities = map Universal_Key.Named_Theorem names
              val keys = map (Universal_Key.key_of (SOME thm_cache) context) entities
           (* val _ = Semantic_Store.interpret_entities context entities
              val _ = Semantic_Store.embed_entities context entities *)
          in keys ~~ names end),
        timeout = NONE
      }

      val check_looping_rules_callback = {
        name = "IsaMini.check_looping_rules",
        arg_schema = unpackTuple4 (
          unpackString,            (* state_id *)
          unpackList unpackString, (* fact_names *)
          unpackBool,              (* simplify_goal *)
          unpackList unpackString  (* premise_names *)
        ),
        ret_schema = packList (packTuple3 (
          packInt,                                                       (* fact index *)
          packString,                                                    (* rule pretty-print *)
          packList (packPair (packString, MiniLang_Agent.pack_raw_term)) (* (pretty, raw_term) *)
        )),
        function = (fn (state_id, fact_names, simplify_goal, premise_names) =>
          let val s0 = get_state state_id
              val ctxt = Minilang.context_of s0
              val thy = Proof_Context.theory_of ctxt
              val SOT = MiniLang_Agent.string_of_term ctxt

              (* Resolve fact names to thms *)
              val facts_thms = map (fn name =>
                Proof_Context.get_thms ctxt name
                handle ERROR _ => []) fact_names

              (* Get target terms to search in *)
              val st = Minilang.leading_proof_sequent_of s0
              val goal_prop = Thm.prop_of st
              val goal_concl = Logic.strip_imp_concl goal_prop
              val prem_terms =
                flat (map (fn name =>
                  map Thm.prop_of (Proof_Context.get_thms ctxt name)
                  handle ERROR _ => []) premise_names)
              val search_terms =
                (if simplify_goal then [goal_concl] else []) @ prem_terms

              (* For each fact, check if any simp rule loops *)
              val results = map_index (fn (i, thms) =>
                let val meta_rules = maps (Raw_Simplifier.mksimps ctxt) thms
                    val looping_rules = filter (fn meta_eq =>
                      let val (lhs, rhs) = Logic.dest_equals
                              (Logic.strip_imp_concl (Thm.prop_of meta_eq))
                      in Minilang.simp_rule_loops thy (lhs, rhs) end
                      handle TERM _ => false) meta_rules
                in
                  if null looping_rules then NONE
                  else
                    let (* Find matching subterms in target terms *)
                        val lhss = map_filter (fn rule =>
                          SOME (fst (Logic.dest_equals
                            (Logic.strip_imp_concl (Thm.prop_of rule))))
                          handle TERM _ => NONE) looping_rules
                        val matches = distinct (fn (a, b) => Term.aconv (a, b))
                          (flat (map (fn lhs =>
                            flat (map (Minilang.find_matching_subterms thy lhs) search_terms)
                          ) lhss))
                        val rule_pretty = SOT (Thm.prop_of (hd thms))
                    in SOME (i, rule_pretty, map (fn t => (SOT t, t)) matches)
                    end
                end) facts_thms
          in map_filter I results
          end handle ERROR msg => error (String.concat ["Error: ", msg])),
        timeout = NONE
      }

      (* Build AoA command with local callbacks *)
      val s0_ptree = Minilang.print_state s0
      val {constants, theorems, types, classes, locales,
           introduction_rules, elimination_rules} =
        Semantic_Store.make_entity_callbacks (Context.Proof ctxt)
      val aoa_cmd = {
        name = "IsaMini.AoA",
        arg_schema = (fn (global_context, driver, invocation_id) =>
            let val log_dir = Config.get ctxt AoA_log_dir
                val retrieval_forking = Config.get ctxt AoA_retrieval_forking
                val interactive_retrieval = Config.get ctxt AoA_interactive_retrieval
            in packTuple7 (context_packer ctxt, minilang_tree_packer ctxt, packString, packString, packString, packString, packString)
                          (global_context, s0_ptree, driver, log_dir, invocation_id, retrieval_forking, interactive_retrieval)
            end),
        ret_schema = unpackTuple3 (unpackList MiniLang_Agent.xcmd_unpacker,
                                   unpackOption unpackString,
                                   (fn src => let val ((i,cw,cr,o_,c), src') =
                                      unpackTuple5 (unpackInt,unpackInt,unpackInt,unpackInt,unpackReal) src
                                    in ({input=i,cache_write=cw,cache_read=cr,output=o_,cost=c}, src') end)),
        timeout = NONE,
        callback = [
          mk_callback proof_opr_callback,
          mk_callback reset_state_callback,
          mk_callback lookup_fact_callback,
          mk_callback retrieve_entity_callback,
          mk_callback compute_bindings_callback,
          mk_callback need_intro_callback,
          mk_callback check_term_callback,
          mk_callback schematic_vars_callback,
          mk_callback potential_defs_callback,
          mk_callback abbreviation_defs_callback,
          mk_callback contextual_thms_callback,
          mk_callback validate_prove_in_time_callback,
          mk_callback check_looping_rules_callback,
          Universal_Key.make_universal_key_callback' (SOME thm_cache) (Context.Proof ctxt),
          Config.make_config_lookup_callback (Context.Proof ctxt),
          constants, theorems, types, classes, locales,
          introduction_rules, elimination_rules,
          Context_Callbacks.make_theory_long_name_callback (Context.Proof ctxt),
          Semantic_Store.make_interpret_theory_callback (Context.Proof ctxt)
        ]
      }

      val timer = Timer.startRealTimer ()
      val (xcmds, s1o, {input, cache_write, cache_read, output, cost}) =
            call_command aoa_cmd (global_context, driver, invocation_id)
      val elapsed = Timer.checkRealTimer timer
      val _ = writeln (String.concat [
        "[AoA] input=", Int.toString input,
        " cache_write=", Int.toString cache_write,
        " cache_read=", Int.toString cache_read,
        " output=", Int.toString output,
        " cost=$", Real.fmt (StringCvt.FIX (SOME 4)) cost,
        " time=", Time.toString elapsed, "s"])
   in case s1o
   of SOME s1 => (
   case Symtab.lookup (!state) s1
   of SOME s1' =>
        if Minilang.is_finished s1'
        then let
          in if exists (fn MiniLang_Agent.SORRY_NEXT _ => true
                         | MiniLang_Agent.SORRY_END_ALL _ => true
                         | MiniLang_Agent.SORRY_ONLY => true
                         | _ => false) xcmds
           then error "Internal Error: the returned proofs contains axiomatic sorry."
           else ()
           ; (xcmds, Minilang.conclude ctxt s1')
         end
        else error "Internal Error: the proof state returned by the Agent is not finished"
    | NONE => error "Internal Error: the state returned by the Agent is not found"
  ) | NONE => error "Agent gives up"
  end


(*** REPL App ***)

local open MessagePackBinIO.Unpack
val unpackBudget = unpackTuple4
              (unpackInt, unpackOption unpackInt, unpackInt, unpackOption unpackInt)
        #> apfst (fn (sl, tt, pN, QRL) => ({
              step_limit = sl,
              total_timeout = Option.map Time.fromSeconds tt,
              parallel_runs = pN,
              QUERY_RET_LIMIT = QRL
           } : MiniLang_Agent.budget))
val unpackCfg = unpackPair (unpackBool, unpackBool)
        #> apfst (fn (drafting, gussing_num_typ) => ({
              drafting = drafting,
              gussing_num_typ = gussing_num_typ
           } : MiniLang_Agent.cfg))
 in

fun AoA_REPL_App (cin, cout, toplevel) =
  let open MessagePackBinIO.Unpack MessagePackBinIO.Pack
      fun read packer = let val (ret, cin') = doUnpack packer (!cin)
                         in cin := cin'
                          ; ret
                        end

      val (invocation_id, driver, cfg, log_dir_override) =
            read (unpackTuple4 (unpackString, unpackString,
                    unpackPair (unpackCfg, unpackBudget), unpackOption unpackString))
      val transition = Toplevel.empty
            |> Toplevel.proof (
                  Proof.refine_primitive (fn ctxt => fn sequent =>
                    let val ctxt = case log_dir_override
                                    of SOME dir => Config.put AoA_log_dir dir ctxt
                                     | NONE => ctxt
                        val start_time = Timing.start ()
                     in \<^try>\<open>
                        let val (_, seq) = AoA_RPC (driver, cfg, invocation_id) (ctxt, sequent)
                            val time = Timing.result start_time
                         in REPL_Server.output cout (packTuple3 (packString, packInt, packInt))
                                 ( "success",
                                   Time.toMilliseconds (#elapsed time),
                                   Time.toMilliseconds (#cpu time)
                                 )
                          ; BinIO.StreamIO.flushOut cout
                          ; seq
                        end
                        catch E as Minilang.OPR_FAIL (typ, msg) =>
                            let val typs = case typ of Minilang.INVALID_OPR => "INVALID_OPR : "
                                                     | Minilang.PROOF_FAIL  => "PROOF FAIL : "
                             in REPL_Server.output_err cout (typs ^ msg)
                              ; BinIO.StreamIO.flushOut cout
                              ; raise E
                            end
                          | Remote_Procedure_Calling.Remote_Calling_Failure {message, ...} =>
                            let val time = Timing.result start_time
                             in REPL_Server.output cout (packTuple3 (packString, packInt, packInt))
                                   ( "remote_error",
                                     Time.toMilliseconds (#elapsed time),
                                     Time.toMilliseconds (#cpu time)
                                   )
                              ; BinIO.StreamIO.flushOut cout
                              ; sequent
                            end
                          | ERROR msg =>
                            if msg = "Agent gives up"
                            then let val time = Timing.result start_time
                                  in REPL_Server.output cout (packTuple3 (packString, packInt, packInt))
                                        ( "agent_gives_up",
                                          Time.toMilliseconds (#elapsed time),
                                          Time.toMilliseconds (#cpu time)
                                        )
                                   ; BinIO.StreamIO.flushOut cout
                                   ; sequent
                                 end
                            else ( REPL_Server.output_err cout msg
                                 ; BinIO.StreamIO.flushOut cout
                                 ; raise (ERROR msg) )
                          | E => (
                                REPL_Server.output_err cout (Runtime.exn_message E)
                              ; BinIO.StreamIO.flushOut cout
                              ; raise E )\<close>
                    end)
                  )
      val (_, toplevel') = Toplevel.command_errors false transition toplevel
   in the_default toplevel toplevel'
  end
end

val _ = REPL_Server.register_app "Minilang.AoA" AoA_REPL_App

(*** The tactic ***)

fun is_dummy th =
  let fun chk (Const(\<^const_name>\<open>Pure.term\<close>, _) $ _) = true
        | chk (Const(\<^const_name>\<open>Pure.prop\<close>, _) $ X) = chk X
        | chk _ = false
   in Thm.is_dummy th orelse chk (Thm.prop_of th)
  end

fun method _ (*using*) (ctxt, sequent) = Seq.make (fn () =>
  if is_dummy sequent then NONE
  else let val driver = Config.get ctxt agent_aoa_driver
           val invocation_id = make_invocation_id ()
           val log_dir = Config.get ctxt AoA_log_dir
           val log_path = if log_dir = "" then "(no logging)"
                          else log_dir ^ "/" ^ invocation_id
           val _ = writeln ("Agent-of-Agents (driver: " ^ driver ^ ", logs: " ^ log_path ^ ")")
           (* Unfold locale/class instance goals (needs `standard`) before the agent runs *)
           val sequent =
             if Phi_Sledgehammer_Solver.need_standard_tac ctxt sequent
             then (case SINGLE (Classical.standard_tac ctxt []) sequent of
                     SOME st' => st'
                   | NONE => sequent)
             else sequent
           (* Preprocess: split large goals before handing to the agent *)
           val sequent =
             (case SINGLE (Goal_Preprocess.preprocess_split_tac ctxt) sequent of
                SOME st' => st'
              | NONE => sequent)
        in AoA_RPC (driver, MiniLang_Agent.default_cfg, invocation_id) (ctxt, sequent)
           |> (fn (_, sequent') => SOME (Seq.Result (ctxt, sequent'), Seq.empty))
       end )


(*** Query by name RPC — reuses the AoA query tool's Python core ***)

local open MessagePackBinIO.Pack MessagePackBinIO.Unpack in

fun query_by_name (context : Context.generic) (kind : Universal_Key.entity_kind, name : string)
    : string * bool =
  let
    val cmd : (Universal_Key.entity_kind * string, string * bool)
              Remote_Procedure_Calling.command = {
      name = "IsaMini.query_by_name",
      arg_schema = packPair (Universal_Key.pack_entity_kind', packString),
      ret_schema = unpackPair (unpackString, unpackBool),
      callback = [Universal_Key.make_universal_key_callback context],
      timeout = NONE
    }
  in Remote_Procedure_Calling.call_command cmd (kind, name) end

end (*local*)


end
