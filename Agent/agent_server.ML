(*TODO: name anounymous hyps ""*)

signature MINILANG_AGENT_AoA = sig

type driver = string
val default_driver: driver
val agent_aoa_driver: string Config.T
val AoA_log_dir: string Config.T
val AoA_interactive_retrieval: string Config.T
val AoA_retrieval_forking: string Config.T
val AoA_use_proof_cache: bool Config.T

type state_id = string
type states = Minilang.state Symtab.table

type agent_cost = {input: int, cache_write: int, cache_read: int, output: int,
                   cost: real, tool_calls: int, isabelle_time: real, model_time: real,
                   quota_wait_time: real}
val zero_cost: agent_cost

val AoA_RPC : driver * (MiniLang_Agent.cfg * MiniLang_Agent.budget) * string
           -> Proof.context * thm
           -> MiniLang_Agent.xcmd list * thm * agent_cost

val method : thm list -> context_state -> context_state Seq.result Seq.seq

(* Query entity by kind and name via the AoA query tool's Python core.
   Returns (formatted_text, is_error). *)
val query_by_name : Context.generic ->
  Universal_Key.entity_kind * string -> string * bool

end

structure MiniLang_Agent_AoA : MINILANG_AGENT_AoA = struct

type agent_cost = {
  input: int, cache_write: int, cache_read: int, output: int,
  cost: real, tool_calls: int, isabelle_time: real, model_time: real,
  quota_wait_time: real
}

val zero_cost : agent_cost = {
  input = 0, cache_write = 0, cache_read = 0, output = 0,
  cost = 0.0, tool_calls = 0, isabelle_time = 0.0, model_time = 0.0,
  quota_wait_time = 0.0
}

exception Agent_Give_Up of string * string * agent_cost

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
      val SOS  = MiniLang_Agent.string_of_sort ctxt
   in fn {vars, hyps}:context =>
      let val tfrees = fold (Term.add_tfreesT o snd) vars []
                       |> distinct (op =)
          val tvars_s = fold (Term.add_tvarsT o snd) vars []
                        |> distinct (op =)
          val tvar_list =
                map (fn (n, s) => (n, SOS s)) tfrees
              @ map (fn (ni, s) => (Term.string_of_vname ni, SOS s)) tvars_s
       in packTuple3
            (packPairList (packString, packString o SOTT),
             packPairList (packString, packString),
             packPairList (packString, packString o SOT))
            (vars, tvar_list, hyps)
      end
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
(* Flat goal packer — replaces the recursive `minilang_tree_packer`.
   Sends just (option(items, leading_goal_term), goals_count) instead
   of the full PROP/BUNDL/BLOCK tree.  Python only needs the leading
   goal (for display) and the count (for display + Root init). *)
fun minilang_flat_goal_packer ctxt =
  let val item_packer = minilang_items_packer ctxt
      val term_packer = packString o MiniLang_Agent.string_of_term ctxt
   in fn (SOME (items, leading_goal), count) =>
        packTuple3 (packInt, packPair (item_packer, term_packer), packInt)
                    (1, (items, leading_goal), count)
       | (NONE, _) =>
        packInt 0
  end

fun minilang_message_packer ctxt =
  let val minilang_items_packer = minilang_items_packer ctxt
      val string_of_term = MiniLang_Agent.string_of_term ctxt
      val string_of_type = MiniLang_Agent.string_of_type ctxt
      fun pack (Minilang.New_Items items) =
            packPair (packInt, minilang_items_packer) (0, items)
        | pack (Minilang.Goals goals) =
            (* Python side only reads the count (for SubgoalMaker's
               `new_subgoals_count`), not the term texts.  Packing just
               the length avoids calling `string_of_term` on every goal
               (expensive for large terms) and shrinks wire size.  The
               full `term list` is still kept on the ML side — the
               translator still consumes it via `item_reporter` for its
               `(*goal: …*)` diagnostic annotations. *)
            packPair (packInt, packInt) (1, length goals)
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
             | Minilang.DROPPED_INSERTION_FACTS names =>
                 packPair (packInt, packList packString) (12, names)
             | MiniLang_Agent.SETUP_REWRITING_MAY_LOOP => packInt 13
             | MiniLang_Agent.COMPUTE_RESULT (name, result) =>
                 packPair (packInt, packPair (packString, packString))
                          (14, (name, result))
             | Minilang.SH_PRF (prf, time) =>
                 packPair (packInt, packPair (packString, packInt))
                          (15, (prf, Time.toMilliseconds time))
             | _ => error "BUG #adli: unexpected Internal message")
   in packList pack o filter (fn Minilang.Internal (MiniLang_Agent.INTRO_BINDINGS _) => true
                                 | Minilang.Internal MiniLang_Agent.SIMPLIFY_FALLBACK_NOSYS => true
                                 | Minilang.Internal MiniLang_Agent.SIMPLIFY_FALLBACK_ONCE_SIMPROC => true
                                 | Minilang.Internal (MiniLang_Agent.SIMPLIFY_TARGETS_STALE _) => true
                                 | Minilang.Internal (MiniLang_Agent.SPECIALIZE_RESULT _) => true
                                 | Minilang.Internal Minilang.PAT_COMPLETENESS_PROOF_OPENED => true
                                 | Minilang.Internal Minilang.TERMINATION_PROOF_OPENED => true
                                 | Minilang.Internal (MiniLang_Agent.DEFINE_RESULT _) => true
                                 | Minilang.Internal (Minilang.DROPPED_INSERTION_FACTS _) => true
                                 | Minilang.Internal MiniLang_Agent.SETUP_REWRITING_MAY_LOOP => true
                                 | Minilang.Internal (MiniLang_Agent.COMPUTE_RESULT _) => true
                                 | Minilang.Internal (Minilang.SH_PRF _) => true
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
   "no"             — direct results, no forking (default)
   "yes"            — fork-based interaction, fork can only answer
   "yes_recursive"  — fork-based interaction, fork can also search *)
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

(* Whether the `aoa` method may READ from the proof cache.
   true (default) — consult both cache levels (L1 Python SQLite, L2 ML
   Phi_Cache_DB) before running the agent, replaying a hit if found.
   false           — bypass cache lookup entirely and always run the agent.
   Writing is unaffected: a finished proof is still stored into BOTH levels
   on success regardless of this option. *)
val AoA_use_proof_cache = Attrib.setup_config_bool \<^binding>\<open>AoA_use_proof_cache\<close>
      (K true);

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
      val _ = Remote_Procedure_Calling.load ["IsaMini.AoA"]

      (* Shared state for all callbacks *)
      val counters = {
        prem_counter = Synchronized.var "prem_counter" 0
      } : MiniLang_Agent.counters
      val replay_mode = Unsynchronized.ref false
      val messages = Unsynchronized.ref []
      fun listen_report msg = messages := msg :: !messages
      fun clean_report () =
        let val ret = rev (!messages)
         in messages := []; ret end

      (* Configure context *)
      val ctxt = ctxt0
            |> Config.put Minilang.strict_end true
            |> Config.put Minilang.counter_mode "none"
            |> Config.put Minilang.INTRO_mk_block true
            (* Keep `transparent_intro` off so `CONSIDER' = CONSIDER'i ∘
               TRANSPARENT_INTRO'` does NOT invoke INTRO' internally.  If it
               did, INTRO'' would emit a second `Goals` for the same
               CONSIDER op and break the Python SubgoalMaker invariant that
               every operation emits `Goals` exactly once.  Default is
               already `false` (library/proof.ML:389); we set it explicitly
               as belt-and-suspenders. *)
            |> Config.put Minilang.transparent_intro false
            |> Config.put Minilang.auto_deconflict_bound true
            |> Config.put Minilang.deconflict_case_fixes true
            |> Config.put Minilang.high_auto_mode true
            |> Config.put Minilang.auto_calculation false
            |> Config.put Printer.show_markup false
            |> Config.put Phi_Cache_DB.enable_proof_cache false
            (* Under `subgoals`, an induction / case-split rule with
             * `consumes > 0` and insufficient `using` facts yields
             * `Prem<i>` subgoals for the agent to discharge through its
             * normal proof flow, instead of erroring out. Schematic vars
             * in those premises trigger an instantiation prompt on the
             * Python side before induction runs. *)
            |> Config.put Minilang.consumes_policy "subgoals"
            (* Auto-insert is disabled on the agent path: the Induction
             * tool arg carries an explicit `facts_to_generalize` field,
             * giving the LLM control over which local facts flow into
             * the induction hypothesis. Letting auto-insert also fire
             * would silently expand that set and mask over-selection
             * mistakes. The ML-level mechanism in library/proof.ML
             * stays intact for non-agent callers. *)
            |> Config.put Minilang.induct_auto_insert_facts false
      val (agent_cfg, _) = cfg
      val ctxt = case #auto_interpret_for_embedding agent_cfg of
                    SOME v => Config.put Semantic_Store.auto_interpret_for_embedding v ctxt
                  | NONE => ctxt

      val global_context = global_context_of (ctxt, sequent)
      val s0 = Minilang.INIT ctxt sequent
      val state = Unsynchronized.ref (Symtab.make [("$init", s0)])

      (* Helper: Get state from table *)
      fun get_state state_id =
        case Symtab.lookup (!state) state_id of
          SOME s => s
        | NONE => error "beginning_state_not_found"

      val agent_context_unpacker : Context_Callbacks.context_unpacker =
        fn src =>
          case MessagePackBinIO.Unpack.unpackOption MessagePackBinIO.Unpack.unpackString src of
            (NONE, src') => (Context.Proof ctxt, src')
          | (SOME sid, src') =>
              (Context.Proof (Minilang.context_of (get_state sid)), src')

      (* Local callback definitions - all share state, counters, messages via closure *)

      val proof_opr_callback = {
        name = "IsaMini.proof_opr",
        arg_schema = unpackTuple3 (unpackString, unpackString, MiniLang_Agent.xcmd_unpacker),
        ret_schema = (fn (ctxt, msgs, flat_goal) =>
          packPair (minilang_message_packer ctxt, minilang_flat_goal_packer ctxt) (msgs, flat_goal)),
        function = (fn (from, to, opr) =>
          let val _ = Minilang.set_reporter listen_report
              val s0 = get_state from
              val (cfg', budget) = cfg
              val mode = if !replay_mode then MiniLang_Agent.REPLAY
                         else MiniLang_Agent.LIVE
              val full_config = (cfg', budget, counters, mode) : MiniLang_Agent.config
              val s1 = MiniLang_Agent.interpret full_config opr s0
              val ctxt' = Minilang.context_of s1
              val msgs = clean_report ()
              val _ = state := Symtab.update (to, s1) (!state)
           in (ctxt', msgs, Minilang.leading_goal_data s1)
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

      val set_replay_mode_callback = {
        name = "IsaMini.set_replay_mode",
        arg_schema = unpackBool,
        ret_schema = packUnit,
        function = (fn mode => replay_mode := mode),
        timeout = NONE
      }

      val lookup_fact_callback = {
        name = "IsaMini.lookup_fact",
        arg_schema = unpackPair (unpackString, unpackList (unpackList (unpackPair (unpackBool, unpack_criterion)))),
        ret_schema = (fn (ctxt, rets) =>
          let val SOT = MiniLang_Agent.string_of_term ctxt
              (* Thm_Name.print emits the same wire format FactRef_to_string did:
                 "name" or "name(i)".  Find_Theorems returns Thm_Name.T since 2025. *)
           in packList (packPair (packString o Thm_Name.print, packString o SOT o Thm.prop_of)) rets
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

      (* All three rule sets use iNet keyed by proposition + aconv post-filter.
         Name-based matching is unreliable: the simpset stores rrule names from
         add-time (via Thm.get_name_hint), which can differ from the fact-table
         name after Global_Theory.name_thms unofficial2 renaming; classical_rule
         derivation strips hints for intro/elim.  For simp, the rrule propositions
         are meta-equalities produced by mksimps — at query time we apply mksimps
         to the queried theorems before matching. *)
      val simp_rule_net : term iNet.net =
        fold (fn (_, thm) =>
          let val p = Thm.prop_of thm
          in iNet.insert_term_safe (op aconv) (p, p) end)
          (#simps (Raw_Simplifier.dest_ss (simpset_of ctxt))) iNet.empty
      val (intro_rule_net : term iNet.net, elim_rule_net : term iNet.net) =
        let (* Declared (original) forms.  Unlike the 2024 nets, dest rules are
               NOT make_elim'd here, so a queried dest theorem now matches the
               elim net and gets the "elim" role (2024 silently never matched
               dest rules because the stored form was the hint-stripped
               make_elim derivative). *)
            fun rules is_elim =
              map #1 (Classical.dest_decls ctxt (fn (_, {kind, ...}) =>
                  Bires.kind_is_elim kind = is_elim andalso not (Bires.kind_extra kind)))
            fun build_net thms =
              fold (fn thm =>
                let val p = Thm.prop_of thm
                in iNet.insert_term_safe (op aconv) (p, p) end) thms iNet.empty
        in (build_net (rules false), build_net (rules true))
        end
      fun in_rule_net net prop =
        exists (fn stored => prop aconv stored) (iNet.match_term net prop)
      fun thm_roles thms =
        let val props = map Thm.prop_of thms
            val simp_props = maps (fn thm =>
                  the_default [] (try (map Thm.prop_of o Raw_Simplifier.mksimps ctxt) thm)) thms
        in (if exists (in_rule_net simp_rule_net) simp_props then ["simp"] else []) @
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
        ret_schema = packList (packOption (packTuple5 (packString, packList packString, packList packString, packList packString, packBool))),
        function = (fn (state_id, entities) =>
          let val s0 = get_state state_id
              val ctxt = Minilang.context_of s0
              val thy = Proof_Context.theory_of ctxt
              val SOT = MiniLang_Agent.string_of_term ctxt
              val SOTy = MiniLang_Agent.string_of_type ctxt
              val facts = Proof_Context.facts_of ctxt
              (* `global_facts` enumerates only facts visible at the
               * theory level; a `full_name` that does NOT resolve here
               * must have come from the local proof context (assms, IH,
               * named `have`, locale-internal fixes). Used to classify
               * theorem-kind retrievals as local vs global — the
               * `facts_to_generalize` field on the Induction tool
               * filters out globals. *)
              val global_facts = Global_Theory.facts_of thy
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
                       let val thms' = map (Thm.transfer thy) (select_thms thms idx_opt)
                           val base_extern = Facts.extern ctxt facts full_name
                           val short_name = case idx_opt of
                                 SOME i => Thm_Name.print (base_extern, i)
                               | NONE => base_extern
                           val abbrevs = distinct (op =) (maps
                                (abbreviations_in_term ctxt consts
                                  o Thm.prop_of) thms')
                           val is_local =
                              not (is_some (Facts.lookup (Context.Theory thy)
                                              global_facts full_name))
                       in if null thms' then NONE
                          else SOME (short_name,
                                     map (SOT o Thm.prop_of) thms',
                                     thm_roles thms',
                                     abbrevs,
                                     is_local)
                       end
                   | NONE => NONE
                end
              fun retrieve (Universal_Key.TheoremK, name) = retrieve_thm name
                | retrieve (Universal_Key.IntroductionRuleK, name) = retrieve_thm name
                | retrieve (Universal_Key.EliminationRuleK, name) = retrieve_thm name
                | retrieve (Universal_Key.InductionRuleK, name) = retrieve_thm name
                | retrieve (Universal_Key.CaseSplitRuleK, name) = retrieve_thm name
                | retrieve (Universal_Key.ConstantK, name) =
                    if Name_Space.declared const_space (Consts.intern consts name) then
                      let val cname = Consts.intern consts name
                          val short = Name_Space.extern ctxt const_space cname
                          val T = Consts.the_constraint consts cname
                          val abbrevs = if is_some (try (Consts.the_abbreviation consts) cname)
                                        then [cname] else []
                      in SOME (short, [SOTy T], [], abbrevs, false) end
                    else
                      (case Variable.lookup_fixed ctxt name of
                        SOME fq_name =>
                          SOME (Variable.revert_fixed ctxt fq_name,
                            (case Variable.default_type ctxt fq_name of
                               SOME T => [SOTy T]
                             | NONE => []),
                            [], [], true)
                      | NONE => NONE)
                | retrieve (Universal_Key.TypeK, name) =
                    SOME (Name_Space.extern ctxt type_space name, [], [], [], false)
                | retrieve (Universal_Key.ClassK, name) =
                    SOME (Name_Space.extern ctxt class_space name, [], [], [], false)
                | retrieve (Universal_Key.LocaleK, name) =
                    SOME (Name_Space.extern ctxt locale_space name, [], [], [], false)
                | retrieve (Universal_Key.Theorem_CollectionK, name) =
                    (* Collection entity: render name + up to 5 member props, with a
                       "... (N more)" sentinel when there are more.  dynamic_fact_members
                       returns NONE for a stale/non-collection (non-dynamic) name, which
                       drops this entity from the result. *)
                    let val full = Facts.intern facts name
                    in case Context_Callbacks.dynamic_fact_members (Context.Proof ctxt) facts full of
                         NONE => NONE
                       | SOME members =>
                           let val n = length members
                               val shown = map (SOT o Thm.prop_of) (take 5 members)
                               val props = if n > 5
                                           then shown @ ["... (" ^ string_of_int (n - 5) ^ " more)"]
                                           else shown
                           in SOME (Facts.extern ctxt facts full, props, [], [], false) end
                    end
          in map (fn e => the_default NONE (try retrieve e)) entities end),
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
        function = (fn (state_id, _) =>
          let val s0 = get_state state_id
           in MiniLang_Agent.check_need_intro s0
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
                  |> map (fn (name, ty) =>
                            (Name.clean (Variable.revert_fixed ctxt name),
                             string_of_type ty))
              val vars = Term.add_vars parsed_term []
                  |> map (fn (name_idx, ty) =>
                          (Term.string_of_vname name_idx, string_of_type ty))
           in (type_string, frees, vars)
          end handle ERROR msg => error (String.concat ["Unparsed: ", msg])
            | TERM (msg, _) => error (String.concat ["Unparsed: ", msg])
            | TYPE (msg, _, _) => error (String.concat ["Unparsed: ", msg])),
        timeout = NONE
      }

      (* Pre-flight predicate for the auto-Intro-before-Induction feature:
       * does the induction `target` mention a free variable that is a
       * not-yet-introduced leading ∀/⋀ binder of the current goal?  Decided
       * entirely in one context: parse the target here, strip the leading
       * binders of THIS goal (raw Abs names, no deconflict), and check
       * membership — avoiding any cross-pipeline name reconciliation on the
       * Python side.  `Variable.is_fixed` excludes a target that is actually
       * an already-fixed (declarable) variable, which inducts fine. *)
      val induction_target_hits_binder_callback = {
        name = "IsaMini.induction_target_hits_leading_binder",
        arg_schema = unpackPair (unpackString, unpackString),
        ret_schema = packBool,
        function = (fn (state_id, target) =>
          let val s0 = get_state state_id
              val ctxt = Minilang.context_of s0
           in if not (MiniLang_Agent.check_need_intro s0) then false
              else
                let val target_term = MiniLang_Agent.read_term ctxt target
                    val frees = Term.add_frees target_term []
                    val goal = Thm.prop_of (Minilang.leading_proof_sequent_of s0)
                                 |> Logic.dest_implies |> fst
                    val (binders, _, _) = Minilang.strip_meta_and_hol_hhf goal
                    val binder_names = map fst binders
                 in exists (fn (nm, _) =>
                      not (Variable.is_fixed ctxt nm)
                      andalso member (op =) binder_names nm) frees
                end
          end handle ERROR _ => false
                   | TERM _ => false
                   | TYPE _ => false),
        timeout = NONE
      }

      val unfold_syntax_callback = {
        name = "IsaMini.unfold_syntax",
        arg_schema = unpackPair (unpackString, unpackString),
        ret_schema = packTuple4 (packString, packString, packString, packString),
        function = (fn (state_id, term_str) =>
          let val s0 = get_state state_id
              val ctxt = Minilang.context_of s0
              val parsed_term = MiniLang_Agent.read_term ctxt term_str
              val head = Term.head_of parsed_term
              val head_name = case head of Const (name, _) => name | _ => ""
              (* Head of the abbreviation-preserving (mode_abbrev) parse: when the
                 term's head is an abbreviation, this names the abbreviation
                 constant itself while head_name names its expansion's head.
                 "" when the abbrev parse fails or the head is not a Const. *)
              val abbrev_head =
                \<^try>\<open>
                  (case Term.head_of (MiniLang_Agent.read_term_abbrev ctxt term_str) of
                     Const (name, _) => name
                   | _ => "")
                 catch _ => ""\<close>
              val raw_display = MiniLang_Agent.string_of_term_main_syntax parsed_term
              val normal_display = MiniLang_Agent.string_of_term ctxt parsed_term
          in (head_name, raw_display, normal_display, abbrev_head)
          end handle ERROR msg => error (String.concat ["Unparsed: ", msg])
            | TERM (msg, _) => error (String.concat ["Unparsed: ", msg])
            | TYPE (msg, _, _) => error (String.concat ["Unparsed: ", msg])),
        timeout = NONE
      }

      (* Resolve a bare notation symbol (e.g. "*", "\<le>", "\<^sup>*") to the
         underlying constant name, covering all fixities via ordered probes:
         operator section, infix, prefix, postfix, then a simple binder form.
         The first probe that parses to a `Const` head wins (so e.g. "-" resolves
         to its infix reading, subtraction, before the prefix reading uminus).
         Probes parse in mode_abbrev: a notation attached to an abbreviation
         resolves to the abbreviation constant itself (e.g. "\<noteq>" yields
         HOL.not_equal, not the expansion's head HOL.Not) — abbreviations are
         first-class entities with their own semantics.
         Returns "" when no probe resolves — callers treat that as "not a
         resolvable notation" and fall back. Unlike `unfold_syntax`, this NEVER
         raises on an unparseable probe: each probe is guarded, because feeding a
         bare symbol is expected to fail for most templates. *)
      val resolve_notation_callback = {
        name = "IsaMini.resolve_notation",
        arg_schema = unpackPair (unpackString, unpackString),
        ret_schema = packString,
        function = (fn (state_id, sym) =>
          let val s0 = get_state state_id
              val ctxt = Minilang.context_of s0
              val probes =
                ["(" ^ sym ^ ")",            (* operator section, e.g. \<le> *)
                 "xPa " ^ sym ^ " yPb",      (* infix:   _ OP _ *)
                 sym ^ " xPa",               (* prefix:  OP _ *)
                 "xPa " ^ sym,               (* postfix: _ OP *)
                 sym ^ " xPa. xPa"]          (* binder:  OP x. _ *)
              fun head_const_of probe =
                \<^try>\<open>
                  (case Term.head_of (MiniLang_Agent.read_term_abbrev ctxt probe) of
                     Const (name, _) => SOME name
                   | _ => NONE)
                 catch _ => NONE\<close>
          in case get_first head_const_of probes of
               SOME name => name
             | NONE => ""
          end),
        timeout = NONE
      }

      (* Whether `const_full_name` is an abbreviation, and the head constant of
         its expansion (for the query tool's semantics fallback layer).
         Caveats, both deliberate:
         - Consts.the_abbreviation yields the NON-normalized rhs: nested
           abbreviations stay unexpanded, so exp_head may itself be an
           abbreviation. We expand only one layer, relying on abbreviation
           constants being interpreted on a par with ordinary constants.
         - The argument must be an internal (interned) full constant name —
           the callers feed names from resolve_notation / unfold_syntax /
           universal_key_of, which all satisfy this. A short name or xname
           silently yields (false, ""). *)
      val abbrev_expansion_head_callback = {
        name = "IsaMini.abbrev_expansion_head",
        arg_schema = unpackPair (unpackString, unpackString),
        ret_schema = packPair (packBool, packString),
        function = (fn (state_id, const_name) =>
          let val s0 = get_state state_id
              val ctxt = Minilang.context_of s0
              val consts = Proof_Context.consts_of ctxt
          in case try (Consts.the_abbreviation consts) const_name of
               SOME (_, rhs) =>
                 (true,
                  case Term.head_of (Term.strip_abs_body rhs) of
                    Const (name, _) => name
                  | _ => "")
             | NONE => (false, "")
          end),
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

      (* All free variables of the ENTIRE leading goal (premises ⟹ conclusion),
       * reverted to agent-facing names. Used by the Induction pre-flight to
       * restrict the variable-classification offer to variables that actually
       * appear in the goal, rather than every in-scope fixed variable (which
       * would include the lemma's `fixes` signature). *)
      val goal_variables_callback = {
        name = "IsaMini.goal_variables",
        arg_schema = unpackString,
        ret_schema = packList packString,
        function = (fn state_id =>
          let val s0 = get_state state_id
              val ctxt = Minilang.context_of s0
              (* Free variables of the ENTIRE leading goal — premises AND
               * conclusion. Minilang's Intro moves the goal's premises out of
               * the goal term into local hypotheses, so the leading subgoal
               * term holds only the conclusion; we union the conclusion's
               * frees with the in-scope hypotheses' frees to capture
               * premise-only variables. `context_of_leading_goal` targets the
               * LEADING goal specifically (no sibling-subgoal leakage). The
               * reversion must match the context-var names exactly (Python
               * compares by string): `Variable.revert_fixed` WITHOUT
               * `Name.clean`, mirroring how `Newly_Fixed` items are reverted. *)
              val ((_, local_facts), concl) =
                Minilang.context_of_leading_goal (Minilang.print_state s0)
              val frees = fold (fn (_, t) => Term.add_frees t) local_facts
                               (Term.add_frees concl [])
           in frees
                |> map (Variable.revert_fixed ctxt o fst)
                |> distinct (op =)
          end handle ERROR msg => error (String.concat ["goal_variables: ", msg])
            | TERM (msg, _) => error (String.concat ["goal_variables: ", msg])
            | TYPE (msg, _, _) => error (String.concat ["goal_variables: ", msg])),
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
              (* Drop infrastructure / unciteable ("??.") definitions, mirroring
                 the filter applied to the semantic-search enumeration path. The
                 fact ref name may carry a "(i)" selector; strip it before the
                 name-based infra checks (the "??." extern test included). *)
              val {is_infra_thm, ...} = Infra_Filter.gen_infra_filters (Context.Proof ctxt)
              fun strip_sel s =
                case String.tokens (fn c => c = #"(") s of base :: _ => base | [] => s
              val results = List.concat (map (fn term =>
                let val parsed_term = MiniLang_Agent.read_term ctxt term
                    val const_name = case Term.head_of parsed_term of
                                       Const (name, _) => name
                                     | Free (name, _) => name
                                     | _ => error "term_head_not_const"
                    val defs = Minilang.potential_defs_of_const ctxt const_name
                 in map_filter (fn (name, thm) =>
                      let val ext = Facts.extern ctxt facts name
                      in if String.isPrefix "??." ext
                            orelse is_infra_thm (strip_sel name, thm)
                         then NONE
                         else SOME (name, ext, SOT (Thm.prop_of thm))
                      end) defs
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
              val (goal_opt, _) = Minilang.leading_goal_data s
              val facts = case goal_opt of
                  SOME ((_, facts), _) => facts
                | NONE => []
              val names = map fst facts
              val entities = map Universal_Key.Named_Theorem names
              val keys = map (Universal_Key.key_of (SOME thm_cache) context) entities
           (* val _ = Semantic_Store.interpret_entities context entities
              val _ = Semantic_Store.embed_entities context entities *)
          in keys ~~ names end),
        timeout = NONE
      }

      val fact_propositions_callback = {
        name = "IsaMini.fact_propositions",
        arg_schema = unpackPair (unpackString, unpackList unpackString),
        ret_schema = packList (packPair (packString, packString)),
        function = (fn (state_id, names) =>
          let val ctxt = Minilang.context_of (get_state state_id)
              val SOT  = MiniLang_Agent.string_of_term ctxt
          in map_filter (fn nm =>
               case the_default [] (try (MiniLang_Agent.read_thms ctxt) nm) of
                   [] => NONE
                 | th :: _ => SOME (nm, SOT (Thm.prop_of th))) names
          end),
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

              (* Resolve fact names to thms (supports [where ...] attributes) *)
              val facts_thms = map (fn name =>
                the_default [] (try (MiniLang_Agent.read_thms ctxt) name)) fact_names

              (* Get target terms to search in *)
              val st = Minilang.leading_proof_sequent_of s0
              val goal_prop = Thm.prop_of st
              val goal_concl = Logic.strip_imp_concl goal_prop
              val prem_terms =
                flat (map (fn name =>
                  map Thm.prop_of (the_default [] (try (Proof_Context.get_thms ctxt) name))) premise_names)
              val search_terms =
                (if simplify_goal then [goal_concl] else []) @ prem_terms

              (* For each fact, check if any simp rule loops *)
              val results = map_index (fn (i, thms) =>
                let val meta_rules = maps (Raw_Simplifier.mksimps ctxt) thms
                    val looping_rules = filter (fn meta_eq =>
                      Looping_Simp.simp_rule_may_loop
                        {only_check_local = false, ignore_cond = false, local_ignore_cond = true,
                         schematize_local_frees = false}
                        ctxt (Thm.prop_of meta_eq)
                    ) meta_rules
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
                            flat (map (PLPR_Pattern.find_matching_subterms thy [] lhs) search_terms)
                          ) lhss))
                        val rule_pretty = SOT (Thm.prop_of (hd thms))
                    in SOME (i, rule_pretty, map (fn t => (SOT t, t)) matches)
                    end
                end) facts_thms
          in map_filter I results
          end handle ERROR msg => error (String.concat ["Error: ", msg])),
        timeout = NONE
      }

      (* Shared result packer + formatter for the analyze_* callbacks.
       * Return shape: Option<(rule_name_opt, consumes, consume_premises,
       *                      remaining_premises, schematic_vars)>.
       * `consume_premises` / `remaining_premises` are pretty-printed;
       * `schematic_vars` is the list of (varname, type) pairs appearing
       * inside consume_premises (the vars the user must either instantiate
       * or discharge via `using`). *)
      (* Return shape: a TRIPLE <dirty_var_names, relevant_facts, analysis>.
       * `dirty_var_names` = the variables a relevant fact may mention (the
       * induction target's frees ∪ `arbitrary`); shown in the picker prompt.
       * `relevant_facts` (the named local facts mentioning those vars; empty
       * for case-split) and `dirty_var_names` are carried OUTSIDE the analysis
       * option, so they are delivered even when no named rule is picked
       * (`analyze_*` returns NONE) — the common case for default structural
       * inductions. `analysis` keeps its original 5-tuple-option shape
       * (rule_name, consumes, consume_prems, remaining_prems, schematic_vars). *)
      val analyze_ret_schema =
        packTuple3 (
          packList packString,
          packList (packPair (packString, packString)),
          packOption (packTuple5 (
            packOption packString,
            packInt,
            packList packString,
            packList packString,
            packList (packPair (packString, packString)))))
      fun format_analysis ctxt (opt : Minilang.induct_analysis option) =
        case opt of
          NONE => NONE
        | SOME {rule_name, consumes, consume_premises, remaining_premises, ...} =>
            let val sot = MiniLang_Agent.string_of_term ctxt
                val sotyp = MiniLang_Agent.string_of_type ctxt
                val schematic_vars =
                  fold Term.add_vars consume_premises []
                  |> distinct (op =)
                  |> map (fn (name_idx, ty) =>
                          (Term.string_of_vname name_idx, sotyp ty))
            in SOME (rule_name, consumes,
                     map sot consume_premises,
                     map sot remaining_premises,
                     schematic_vars) end
      fun analyze_error callback_name msg =
        error (String.concat [callback_name, ": ", msg])

      (* Pre-flight analysis for INDUCT. *)
      val analyze_induct_callback = {
        name = "IsaMini.analyze_induct",
        arg_schema = unpackTuple5 (
          unpackString,                                 (* state_id *)
          unpackString,                                 (* target term *)
          unpackList (unpackOption unpackString),       (* vars (opt_var_names) *)
          unpackList unpackString,                      (* arbitrary (term strings, expected Free) *)
          unpackOption unpackString                     (* rule name *)
        ),
        ret_schema = analyze_ret_schema,
        function = (fn (state_id, target, _, arbitrary, rule_name_opt) =>
          let val s0 = get_state state_id
              val ctxt = Minilang.context_of s0
              val sot = MiniLang_Agent.string_of_term ctxt
              val target_term = MiniLang_Agent.read_term ctxt target
              val arbitrary_terms = map (MiniLang_Agent.read_term ctxt) arbitrary
              val arbitrary_vs = map (fn Free nt => nt
                                       | x => error ("The `arbitrary` argument must be variables, \
                                                     \but (" ^ sot x ^ ") is given.")) arbitrary_terms
              val opt_rule = Option.map
                 (fn nm => [Proof_Context.get_thm ctxt nm]) rule_name_opt
              (* Match the INDUCT arg shape in Agent/agent.ML's dispatcher. *)
              val args = (false, ([[SOME (NONE, (target_term, false))]],
                                  (([arbitrary_vs], []), opt_rule)))
              (* Candidate IH facts: in-scope local facts whose proposition
               * mentions the induction target ∪ `arbitrary` vars. Read straight
               * from the leading goal's `local_facts`, which already carries one
               * (name, prop) entry per theorem with the standard indexed name
               * (`h`, or `h(1)`/`h(2)` for a multi-thm fact — see
               * Minilang_Aux.flatten_facts). So every DIRTY theorem of a
               * multi-thm fact is surfaced under its own selectable, 1-based
               * `h(i)` name, which the carry-through (retrieve_entity /
               * Attrib.eval_thms) resolves. *)
              val dirty_frees = Term.add_frees target_term arbitrary_vs
              val dirty = member (op =) dirty_frees
              val ((_, local_facts), _) =
                Minilang.context_of_leading_goal (Minilang.print_state s0)
              (* Keep only the INNERMOST binding for each name: a name shared
               * across nested scopes resolves (in the carry-through, via
               * Facts.lookup) to the innermost one. `context_of_leading_goal`
               * lists outer→inner, so `fold_rev` (right-to-left) keeps the
               * rightmost (innermost) occurrence while rebuilding left-to-right
               * display order. *)
              val dedup_facts =
                fold_rev (fn (n, t) => fn acc =>
                            if AList.defined (op =) acc n then acc
                            else (n, t) :: acc)
                         local_facts []
              val relevant_facts =
                dedup_facts
                |> filter (fn (_, t) =>
                     Term.exists_subterm (fn Free f => dirty f | _ => false) t)
                |> map (fn (name, t) => (name, sot t))
              (* Revert internal fixed-var names (`n__`) to the agent-facing
               * names (`n`) for the picker prompt. *)
              val dirty_var_names =
                dirty_frees |> map (Variable.revert_fixed ctxt o fst)
                            |> distinct (op =)
          in (dirty_var_names, relevant_facts,
              format_analysis ctxt (Minilang.analyze_induct ctxt args []))
          end handle ERROR msg => analyze_error "analyze_induct" msg
                   | TERM (msg, _) => analyze_error "analyze_induct" msg
                   | TYPE (msg, _, _) => analyze_error "analyze_induct" msg),
        timeout = NONE
      }

      (* Pre-flight analysis for CASE_SPLIT. Mirrors analyze_induct but with
       * no `arbitrary` argument and a single-thm rule. *)
      val analyze_case_split_callback = {
        name = "IsaMini.analyze_case_split",
        arg_schema = unpackTuple4 (
          unpackString, unpackString,
          unpackList (unpackOption unpackString),
          unpackOption unpackString
        ),
        ret_schema = analyze_ret_schema,
        function = (fn (state_id, target, _, rule_name_opt) =>
          let val s0 = get_state state_id
              val ctxt = Minilang.context_of s0
              val target_term = MiniLang_Agent.read_term ctxt target
              val opt_rule = Option.map (Proof_Context.get_thm ctxt) rule_name_opt
              (* Match the CASE_SPLIT arg shape in Agent/agent.ML's dispatcher. *)
              val args = (false, ([[SOME target_term]], opt_rule))
          in ([], [], format_analysis ctxt (Minilang.analyze_case_split ctxt args []))
          end handle ERROR msg => analyze_error "analyze_case_split" msg
                   | TERM (msg, _) => analyze_error "analyze_case_split" msg
                   | TYPE (msg, _, _) => analyze_error "analyze_case_split" msg),
        timeout = NONE
      }

      (* Pre-flight validation for schematic-variable instantiation of an
       * induction / case-split rule. Takes the rule name and a list of
       * (var_name, term_string) pairs; attempts the structured
       * instantiation via Rule_Insts.where_rule (with show_sorts enabled
       * for informative error messages). Returns NONE on success, or
       * SOME error_msg on failure. *)
      val validate_instantiation_callback = {
        name = "IsaMini.validate_instantiation",
        arg_schema = unpackTuple3 (
          unpackString,                                 (* state_id *)
          unpackString,                                 (* rule name *)
          unpackList (unpackPair (unpackString, unpackString)) (* (var, term) instantiations *)
        ),
        ret_schema = packOption packString,
        function = (fn (state_id, rule_name, insts) =>
          let val s0 = get_state state_id
              val ctxt = Minilang.context_of s0
                         |> Config.put show_sorts true
              val raw_rule = Proof_Context.get_thm ctxt rule_name
              fun parse_var v =
                case Lexicon.read_variable v of
                  SOME ix => ix
                | NONE => error ("Malformed schematic variable name: `" ^ v ^ "`")
              val raw_insts =
                map (fn (v, t) => ((parse_var v, Position.none), t)) insts
          in
            (Rule_Insts.where_rule ctxt raw_insts [] raw_rule; NONE)
            handle ERROR msg => SOME msg
          end),
        timeout = NONE
      }

      (* Build AoA command with local callbacks *)
      val goal_hash = Hasher.goal (ctxt, sequent)
      val thy = Proof_Context.theory_of ctxt
      val aoa_cache_key = "aoa:" ^ goal_hash
      val use_cache = Config.get ctxt AoA_use_proof_cache
      val cached_xcmd_json =
            if use_cache
            then case Phi_Cache_DB.get_cached_proof thy aoa_cache_key of
                    SOME (_, json) => SOME json
                  | NONE => NONE
            else NONE
      val _ = tracing (String.concat [
        "[AoA-cache] L2 Phi_Cache_DB get key=", aoa_cache_key,
        " thy=", Context.theory_name {long=true} thy,
        " : ", (if not use_cache then "BYPASSED (AoA_use_proof_cache=false)"
                else case cached_xcmd_json
                  of SOME json => "HIT (" ^ Int.toString (size json) ^ "B)"
                   | NONE => "MISS")])

      val s0_flat_goal = Minilang.leading_goal_data s0
      val au = agent_context_unpacker
      val {constants, theorems, types, classes, locales, named_theorems, methods,
           introduction_rules, elimination_rules,
           induction_rules, case_split_rules} =
        Semantic_Store.make_entity_callbacks (Context.Proof ctxt) au
      val aoa_cmd = {
        name = "IsaMini.AoA",
        arg_schema = (fn (global_context, driver, invocation_id) =>
            let val log_dir = Config.get ctxt AoA_log_dir
                val retrieval_forking = Config.get ctxt AoA_retrieval_forking
                val interactive_retrieval = Config.get ctxt AoA_interactive_retrieval
                val (_, budget) = cfg
            in packTuple10 (context_packer ctxt, minilang_flat_goal_packer ctxt,
                           packString, packString, packString, packString, packString,
                           packTuple3 (packInt, packInt, packInt),
                           packString, packPair (packBool, packOption packString))
                          (global_context, s0_flat_goal, driver, log_dir, invocation_id,
                           retrieval_forking, interactive_retrieval,
                           (#timeout_seconds budget, #max_tool_calls budget, #max_retries budget),
                           goal_hash, (use_cache, cached_xcmd_json))
            end),
        ret_schema = unpackTuple6 (unpackList MiniLang_Agent.xcmd_unpacker,
                                   unpackOption unpackString,
                                   (fn src => let val ((i,cw,cr,o_,c,tc,it,mt,qwt), src') =
                                      unpackTuple9 (unpackInt,unpackInt,unpackInt,unpackInt,unpackReal,unpackInt,unpackReal,unpackReal,unpackReal) src
                                    in ({input=i,cache_write=cw,cache_read=cr,output=o_,cost=c,tool_calls=tc,isabelle_time=it,model_time=mt,quota_wait_time=qwt}, src') end),
                                   unpackOption unpackString,
                                   unpackOption unpackString,
                                   unpackOption unpackString),
        timeout = NONE,
        callback = [
          mk_callback proof_opr_callback,
          mk_callback reset_state_callback,
          mk_callback set_replay_mode_callback,
          mk_callback lookup_fact_callback,
          mk_callback retrieve_entity_callback,
          mk_callback compute_bindings_callback,
          mk_callback need_intro_callback,
          mk_callback check_term_callback,
          mk_callback induction_target_hits_binder_callback,
          mk_callback unfold_syntax_callback,
          mk_callback resolve_notation_callback,
          mk_callback abbrev_expansion_head_callback,
          mk_callback schematic_vars_callback,
          mk_callback goal_variables_callback,
          mk_callback potential_defs_callback,
          mk_callback abbreviation_defs_callback,
          mk_callback analyze_induct_callback,
          mk_callback analyze_case_split_callback,
          mk_callback validate_instantiation_callback,
          mk_callback contextual_thms_callback,
          mk_callback fact_propositions_callback,
          mk_callback validate_prove_in_time_callback,
          mk_callback check_looping_rules_callback,
          Universal_Key.make_universal_key_callback' (SOME thm_cache) au,
          Config.make_config_lookup_callback au,
          constants, theorems, types, classes, locales, named_theorems, methods,
          introduction_rules, elimination_rules,
          induction_rules, case_split_rules,
          Context_Callbacks.make_theory_long_name_callback au,
          Semantic_Store.make_interpret_theory_callback au
        ]
      }

      val timer = Timer.startRealTimer ()
      val (xcmds, s1o, {input, cache_write, cache_read, output, cost, tool_calls, isabelle_time, model_time, quota_wait_time}, reason, detail, proof_json_opt) =
            call_command aoa_cmd (global_context, driver, invocation_id)
      val elapsed = Timer.checkRealTimer timer
      val _ = writeln (String.concat [
        "[AoA] input=", Int.toString input,
        " cache_write=", Int.toString cache_write,
        " cache_read=", Int.toString cache_read,
        " output=", Int.toString output,
        " cost=$", Real.fmt (StringCvt.FIX (SOME 4)) cost,
        " tool_calls=", Int.toString tool_calls,
        " isabelle_time=", Real.fmt (StringCvt.FIX (SOME 2)) isabelle_time, "s",
        " model_time=", Real.fmt (StringCvt.FIX (SOME 2)) model_time, "s",
        " quota_wait_time=", Real.fmt (StringCvt.FIX (SOME 2)) quota_wait_time, "s",
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
           ; (case proof_json_opt of
                SOME json => (
                  tracing (String.concat [
                    "[AoA-cache] L2 Phi_Cache_DB store key=", aoa_cache_key,
                    " thy=", Context.theory_name {long=true} thy,
                    " bytes=", Int.toString (size json)]);
                  Phi_Cache_DB.update_cached_proof thy
                               (aoa_cache_key, (elapsed, json)))
              | NONE => tracing "[AoA-cache] L2 Phi_Cache_DB store SKIPPED (proof_json=NONE)")
           ; (xcmds, Minilang.conclude ctxt s1',
              {input=input, cache_write=cache_write, cache_read=cache_read, output=output,
               cost=cost, tool_calls=tool_calls, isabelle_time=isabelle_time, model_time=model_time,
               quota_wait_time=quota_wait_time})
         end
        else error "Internal Error: the proof state returned by the Agent is not finished"
    | NONE => error "Internal Error: the state returned by the Agent is not found"
  ) | NONE =>
        (case reason
          of SOME r => raise Agent_Give_Up (r, the_default "" detail,
                        {input=input, cache_write=cache_write, cache_read=cache_read, output=output,
                         cost=cost, tool_calls=tool_calls, isabelle_time=isabelle_time, model_time=model_time,
                         quota_wait_time=quota_wait_time})
           | NONE => error "Agent gives up (protocol error: missing reason)")
  end


(*** REPL App ***)

local open MessagePackBinIO.Unpack
val unpackBudget = unpackTuple3 (unpackInt, unpackInt, unpackInt)
        #> apfst (fn (ts, mtc, mr) => ({
              timeout_seconds = ts,
              max_tool_calls = mtc,
              max_retries = mr
           } : MiniLang_Agent.budget))
val unpackCfg = unpackOption unpackBool
        #> apfst (fn aie => {auto_interpret_for_embedding = aie} : MiniLang_Agent.cfg)
 in

fun AoA_REPL_App (cin, cout, toplevel) =
  let open MessagePackBinIO.Unpack MessagePackBinIO.Pack
      fun read packer = let val (ret, cin') = doUnpack packer (!cin)
                         in cin := cin'
                          ; ret
                        end

      val (invocation_id, driver, cfg, log_dir_override,
           retrieval_forking_override, interactive_retrieval_override) =
            read (unpackTuple6 (unpackString, unpackString,
                    unpackPair (unpackCfg, unpackBudget), unpackOption unpackString,
                    unpackOption unpackString, unpackOption unpackString))
      val transition = Toplevel.empty
            |> Toplevel.proof (
                  Proof.refine_primitive (fn ctxt => fn sequent =>
                    let val ctxt = case log_dir_override
                                    of SOME dir => Config.put AoA_log_dir dir ctxt
                                     | NONE => ctxt
                        val ctxt = case retrieval_forking_override
                                    of SOME v => Config.put AoA_retrieval_forking v ctxt
                                     | NONE => ctxt
                        val ctxt = case interactive_retrieval_override
                                    of SOME v => Config.put AoA_interactive_retrieval v ctxt
                                     | NONE => ctxt
                        val start_time = Timing.start ()
                        fun cost_tuple ({input, cache_write, cache_read, output,
                                         cost, tool_calls, isabelle_time, model_time,
                                         quota_wait_time} : agent_cost) =
                            (input, cache_write, cache_read, output, cost, tool_calls, isabelle_time, model_time, quota_wait_time)
                        val pack_result =
                              packTuple5 (packString, packInt, packInt,
                                          packOption packString,
                                          packTuple9 (packInt, packInt, packInt, packInt,
                                                      packReal, packInt, packReal, packReal, packReal))
                     in \<^try>\<open>
                        let val (_, seq, aoa_cost) = AoA_RPC (driver, cfg, invocation_id) (ctxt, sequent)
                            val time = Timing.result start_time
                         in REPL_Server.output cout pack_result
                                 ( "success",
                                   Time.toMilliseconds (#elapsed time),
                                   Time.toMilliseconds (#cpu time),
                                   NONE,
                                   cost_tuple aoa_cost
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
                             in REPL_Server.output cout pack_result
                                   ( "remote_error",
                                     Time.toMilliseconds (#elapsed time),
                                     Time.toMilliseconds (#cpu time),
                                     SOME message,
                                     cost_tuple zero_cost
                                   )
                              ; BinIO.StreamIO.flushOut cout
                              ; sequent
                            end
                          | Agent_Give_Up (reason, detail, aoa_cost) =>
                            let val time = Timing.result start_time
                                val det = if detail = "" then NONE
                                          else SOME detail
                             in REPL_Server.output cout pack_result
                                   ( reason,
                                     Time.toMilliseconds (#elapsed time),
                                     Time.toMilliseconds (#cpu time),
                                     det,
                                     cost_tuple aoa_cost
                                   )
                              ; BinIO.StreamIO.flushOut cout
                              ; sequent
                            end
                          | ERROR msg =>
                            ( REPL_Server.output_err cout msg
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
           |> (fn (_, sequent', _) => SOME (Seq.Result (ctxt, sequent'), Seq.empty))
       end )


(*** Query by name RPC — reuses the AoA query tool's Python core ***)

local open MessagePackBinIO.Pack MessagePackBinIO.Unpack in

fun query_by_name (context : Context.generic) (kind : Universal_Key.entity_kind, name : string)
    : string * bool =
  let
    val su = Context_Callbacks.static_context_unpacker context
    val cmd : (Universal_Key.entity_kind * string, string * bool)
              Remote_Procedure_Calling.command = {
      name = "IsaMini.query_by_name",
      arg_schema = packPair (Universal_Key.pack_entity_kind', packString),
      ret_schema = unpackPair (unpackString, unpackBool),
      callback = [Universal_Key.make_universal_key_callback su],
      timeout = NONE
    }
  in Remote_Procedure_Calling.call_command cmd (kind, name) end

end (*local*)


end
