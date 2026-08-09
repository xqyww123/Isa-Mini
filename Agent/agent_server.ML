(*TODO: name anounymous hyps ""*)

signature MINILANG_AGENT_AoA = sig

type driver = string
val default_driver: driver
val aoa_driver: string Config.T
val AoA_log_dir: string Config.T
val AoA_interactive_retrieval: string Config.T
val AoA_retrieval_forking: string Config.T
val AoA_read_proof_store: bool Config.T
val AoA_write_proof_store: bool Config.T
val AoA_enable_write_memory: bool Config.T

type state_id = string
type states = Minilang.state Symtab.table

type agent_cost = {input: int, cache_write: int, cache_read: int, output: int,
                   cost: real, tool_calls: int, isabelle_time: real, model_time: real,
                   quota_wait_time: real}
val zero_cost: agent_cost

(* The nine-field cost line, shared by the AoA-side tracing print (which appends
   its locally-timed " time=" field) and the phi-side give-up print. *)
val string_of_cost : agent_cost -> string

(* Raised by raw_AoA to signal the agent gave up (surrender/refute/resource
   exhaustion). Exposed so the REPL-app wrapper in the Minilang_AoA_REPL session
   can catch it after the app moved out of this structure.
   Also raised BEFORE any agent starts (with reason "technical_failure" and
   zero_cost) when the goal cannot be brought into an AoA-workable shape —
   e.g. merge_segment (the third preprocessing segment) fails to atomize the
   shared-schematic subgoals. *)
exception Agent_Give_Up of string * string * agent_cost

(* Failure-dispatch banners (PHI_VC_SOLVER D51): one line per give-up reason;
   consumers render `error (banner_of reason ^ "\n" ^ detail)`. *)
val banner_of : string -> string

(* The Minilang configuration shared by live agent runs and `aoa_replay` (D35).
   Twelve unconditional Config.puts; the conditional
   `auto_interpret_for_embedding` put stays with the caller. *)
val configure_for_minilang : Proof.context -> Proof.context

(* The Task: what the agent is asked to do.  Sent to Python as a 2-array
   (kind, payload) — empty payload for Usual, the original Isar proof for
   Learning. *)
datatype task = Usual | Learning of string

(* The AoA gate (D8/D16): AoA may start only under an interactive frontend, or
   with AOA_ALLOW_NONINTERACTIVE=yes.  Checked in raw_AoA's entry (first cell),
   so every caller hits it; replay never passes here (D29). *)
val aoa_allowed : unit -> bool

(* D34/D64: the two DETERMINISTIC preprocessing segments, shared verbatim by
   raw_AoA (recording) and the aoa_replay method (re-run on replay).  The
   nondeterministic split segment between them records a script instead
   (Goal_Preprocess.preprocess_split_recorded / the recorded text on replay). *)
val standard_tac_segment : Proof.context -> thm -> thm
val merge_segment : Proof.context -> thm -> thm

(* raw_AoA — the pure recording entry (§2.3): gate, three preprocessing
   segments, agent RPC.  NO store or cache logic inside.  Synchronous; the
   by-products are (xcmds, cost, replay time, proof text): the third component
   is what a REPLAY of this proof will spend (entry preprocessing + the final
   op stream's summed ML time, undivided by Timeout.scale); the fourth is the
   assembled `aoa_replay "<b64>"` — the blob format is known only to this
   assembler and the aoa_replay decoder.  Futures exist one layer up: run_AoA
   obtains them from async_prove. *)
val raw_AoA : {driver: driver, minilang_cfg: MiniLang_Agent.cfg,
               budget: MiniLang_Agent.budget, invocation_id: string, task: task}
           -> Proof.context * thm
           -> (MiniLang_Agent.xcmd list * agent_cost * Time.time * string) * thm

(* run_AoA — the caching wrapper around raw_AoA:
   [read_store -> level-0 two-level lookup] -> raw_AoA -> [write_store ->
   write-back to L2 and L1].  bool option NONE follows the
   AoA_read_proof_store / AoA_write_proof_store configs.  On a level-0 hit the
   four by-products are ([], zero_cost, recorded time, stored text) in a
   fulfilled Future.value — the agent never ran. *)
val run_AoA : {driver: driver, minilang_cfg: MiniLang_Agent.cfg,
               budget: MiniLang_Agent.budget, invocation_id: string,
               read_store: bool option, write_store: bool option,
               async: bool, task: task}
           -> Proof.context * thm
           -> (MiniLang_Agent.xcmd list * agent_cost * Time.time * string) future * thm

val method : thm list -> context_state -> context_state Seq.result Seq.seq

(* Body of the `aoa_replay` method (registered in Minilang_AoA.thy, D39): pure
   ML replay of an assembled blob — no RPC, no Python.  Fails as a method
   failure (empty sequence). *)
val aoa_replay_method : string (*b64 blob*)
                     -> thm list -> context_state -> context_state Seq.result Seq.seq

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

(* One definition for every cost print (author-finalized format, 2026-08-10):
   phi's give-up path prints exactly this line; the AoA-side tracing line
   appends its locally-timed " time=" field. *)
fun string_of_cost ({input, cache_write, cache_read, output, cost, tool_calls,
                     isabelle_time, model_time, quota_wait_time} : agent_cost) =
  String.concat [
    "[AoA] input=", Int.toString input,
    " cache_write=", Int.toString cache_write,
    " cache_read=", Int.toString cache_read,
    " output=", Int.toString output,
    " cost=$", Real.fmt (StringCvt.FIX (SOME 4)) cost,
    " tool_calls=", Int.toString tool_calls,
    " isabelle_time=", Real.fmt (StringCvt.FIX (SOME 2)) isabelle_time, "s",
    " model_time=", Real.fmt (StringCvt.FIX (SOME 2)) model_time, "s",
    " quota_wait_time=", Real.fmt (StringCvt.FIX (SOME 2)) quota_wait_time, "s"]

exception Agent_Give_Up of string * string * agent_cost

fun banner_of "refute" =
      "Refuted: the proof agent found this proof obligation does not hold:"
  | banner_of "resource_unavailable" =
      "The proof agent could not reach the language model backend. This is an infrastructure failure."
  | banner_of "resource_exhausted" =
      "The proof agent exhausted its budget before finding a proof. This usually means the goal is too hard for the agent to solve."
  | banner_of "surrender" =
      "The proof goal is hard and the proof agent was unable to solve it."
  | banner_of "technical_failure" =
      "The proof agent stopped for a technical reason:"
  | banner_of reason =
      "The proof agent gave up for an unrecognized reason (" ^ reason ^ "):"

type driver = string
val default_driver = "ClaudeCode"

(* Config for driver selection *)
val aoa_driver = Attrib.setup_config_string \<^binding>\<open>AoA_driver\<close> (K default_driver)

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
             | MiniLang_Agent.INTRO_STANDARDIZED =>
                 packInt 16
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
             (* How many facts an interpretation brought in, when there were too
                many to inject into the local items.  They are all registered and
                reachable by name / `query`; this only tells the agent the count. *)
             | Minilang.INTERPRET_FACTS_COUNT n =>
                 packPair (packInt, packInt) (19, n)
             | MiniLang_Agent.SETUP_REWRITING_MAY_LOOP => packInt 13
             | MiniLang_Agent.COMPUTE_RESULT (name, result) =>
                 packPair (packInt, packPair (packString, packString))
                          (14, (name, result))
             | Minilang.SH_PRF (prf, time) =>
                 packPair (packInt, packPair (packString, packInt))
                          (15, (prf, Time.toMilliseconds time))
             | Agent_Hint.HINT_NOTICE {name, text} =>
                 packPair (packInt, packPair (packString, packString))
                          (17, (name, text))
             | Minilang.DISCARDED_VARS pairs =>
                 packPair (packInt, packList (packPair (packString, packString)))
                          (18, pairs)
             | _ => error "BUG #adli: unexpected Internal message")
   in packList pack o filter (fn Minilang.Internal (MiniLang_Agent.INTRO_BINDINGS _) => true
                                 | Minilang.Internal MiniLang_Agent.SIMPLIFY_FALLBACK_NOSYS => true
                                 | Minilang.Internal MiniLang_Agent.SIMPLIFY_FALLBACK_ONCE_SIMPROC => true
                                 | Minilang.Internal MiniLang_Agent.INTRO_STANDARDIZED => true
                                 | Minilang.Internal (MiniLang_Agent.SIMPLIFY_TARGETS_STALE _) => true
                                 | Minilang.Internal (MiniLang_Agent.SPECIALIZE_RESULT _) => true
                                 | Minilang.Internal Minilang.PAT_COMPLETENESS_PROOF_OPENED => true
                                 | Minilang.Internal Minilang.TERMINATION_PROOF_OPENED => true
                                 | Minilang.Internal (MiniLang_Agent.DEFINE_RESULT _) => true
                                 | Minilang.Internal (Minilang.DROPPED_INSERTION_FACTS _) => true
                                 | Minilang.Internal (Minilang.INTERPRET_FACTS_COUNT _) => true
                                 | Minilang.Internal MiniLang_Agent.SETUP_REWRITING_MAY_LOOP => true
                                 | Minilang.Internal (MiniLang_Agent.COMPUTE_RESULT _) => true
                                 | Minilang.Internal (Minilang.SH_PRF _) => true
                                 | Minilang.Internal (Agent_Hint.HINT_NOTICE _) => true
                                 | Minilang.Internal (Minilang.DISCARDED_VARS _) => true
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
  | FactRef_to_string (Fact s) = String.concat ["\<open>", RPC_Pretty.trim_markup s, "\<close>"]
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
   Phi_Proof_Store) before running the agent, replaying a hit if found.
   false           — bypass cache lookup entirely and always run the agent.
   Writing is unaffected: a finished proof is still stored into BOTH levels
   on success regardless of this option. *)
val AoA_read_proof_store = Attrib.setup_config_bool \<^binding>\<open>AoA_read_proof_store\<close>
      (K true);

(* Whether a finished proof is STORED into the caches on success.
   true (default) — write both store levels (L2 ML Phi_Proof_Store, L1 Python
   SQLite).
   false           — skip BOTH writes.  Reading is a separate toggle
   (AoA_read_proof_store). *)
val AoA_write_proof_store = Attrib.setup_config_bool \<^binding>\<open>AoA_write_proof_store\<close>
      (K true);

(* Whether the `write_memory` tool (save a reusable proof experience) is offered
   to the agent at all. true (default) — advertised as before. false — dropped
   from every advertised tool set (Python side), so it never appears in available
   tools, and the LearningTask memorize interaction becomes a no-op. Experience
   RETRIEVAL (`query kinds:["experience"]`) is ALWAYS available regardless. *)
val AoA_enable_write_memory = Attrib.setup_config_bool \<^binding>\<open>AoA_enable_write_memory\<close>
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

(* The Minilang configuration shared by live agent runs and replay (D35):
   `aoa_replay` must interpret a recorded op stream under the exact same
   Minilang semantics the recording session used, so both entries call this
   one function.  The only conditional put (`auto_interpret_for_embedding`)
   stays with the raw_AoA caller — replay never touches the semantic DB. *)
fun configure_for_minilang ctxt = ctxt
      |> Config.put Minilang.strict_end true    (*hard constraint, D32*)
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
      |> Config.put Phi_Proof_Store.enable_proof_store false
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


(*** Task ***)

datatype task = Usual | Learning of string

(* Wire format: the task rides the agent-start arg schema as a 2-array
   (task_kind, payload) — empty payload for Usual, the original Isar proof for
   Learning. *)
fun pack_task Usual = ("usual", MessagePackBinIO.Pack.packString "")
  | pack_task (Learning isar_proof) =
      ("learning", MessagePackBinIO.Pack.packString isar_proof)


(*** The AoA gate (D8/D16) ***)

(* Sits in raw_AoA's entry — the point where an agent would actually start — so
   every caller hits it, including the learning App's direct raw_AoA call.
   Replay is NEVER gated (D29): store-hit replay and `aoa_replay` run before or
   outside this function. *)
fun aoa_allowed () =
      (case #2 (Dialogue.frontend_identity ()) of SOME b => b | NONE => false)
      orelse getenv "AOA_ALLOW_NONINTERACTIVE" = "yes"

(* §6.1 finalized copy, raised at the closed gate.  Line breaks are part of the
   finalized text — keep Pretty.str lines verbatim. *)
fun gate_error (ctxt, sequent) =
  let val thy = Proof_Context.theory_of ctxt
      val store_path = Phi_Proof_Store.store_path thy
      val goal_pretty =
        (case Thm.prems_of sequent of
           x :: _ => Syntax.pretty_term ctxt x
         | [] => Syntax.pretty_term ctxt (Thm.prop_of sequent))
   in error (Pretty.string_of (Pretty.chunks [
        Pretty.str "Unproved obligation, and no usable proof to replay.",
        Pretty.str "",
        Pretty.str ("  theory:     " ^ Context.theory_long_name thy),
        Pretty.block [Pretty.str "  goal:       ", goal_pretty],
        Pretty.str "",
        Pretty.str "The proof store holds no usable proof for this obligation, and the AoA prover is",
        Pretty.str "restricted to interactive editing.",
        Pretty.str "",
        Pretty.str "  If you are an author of this development",
        Pretty.str "    Open the theory in jEdit or VSCode and evaluate it: AoA will search for a proof and",
        Pretty.str ("    record it in " ^ Path.implode store_path ^ "."),
        Pretty.str "    To let AoA run in batch mode instead, set AOA_ALLOW_NONINTERACTIVE=yes.",
        Pretty.str "",
        Pretty.str "  If you are a user of this redistributed package",
        Pretty.str "    The package ships an incomplete or outdated proof store. Please ask the author to",
        Pretty.str "    provide one that covers this theory."
      ]))
  end


(*** D34/D64: the deterministic preprocessing segments, shared verbatim by
     raw_AoA (recording) and the aoa_replay method (re-run on replay).  The
     nondeterministic split segment between them is NOT here: recording uses
     Goal_Preprocess.preprocess_split_recorded, replay executes the recorded
     script. ***)

(* Segment 1 — unfold locale/class instance goals (needs `standard`). *)
fun standard_tac_segment ctxt sequent =
  if Phi_Sledgehammer_Solver.need_standard_tac ctxt sequent
  then (case SINGLE (Classical.standard_tac ctxt []) sequent of
          SOME st' => st'
        | NONE => sequent)
  else sequent

(* Segment 3 — S12-S14: when several top-level subgoals share a schematic
   variable, AoA's per-subgoal proof trees would instantiate it independently
   and the final replay fails only after the whole budget is spent.  Merge such
   subgoals into ONE goal before anything else sees them: atomize each subgoal
   into a HOL proposition and conjoin with HOL.conj (SplitConjs can split those
   back; Pure `&&&` it cannot).  The state is rebuilt by kernel forward
   construction, so it still proves the ORIGINAL conclusion and the exit path
   is untouched.  The store key is computed by the caching layer on the goal
   BEFORE any preprocessing (D59), so only `Minilang.INIT` must still see the
   merged goal — a pure function of (ctxt, sequent), so replay's re-run
   reproduces the recorded state verbatim (D64). *)
fun merge_segment ctxt0 sequent =
  let val prems = Thm.prems_of sequent
      (* Sharing is keyed on indexed names (term and type variables alike),
         matching Minilang.INIT's rejection predicate exactly — so on this
         path every state INIT would reject gets merged (or gives up
         cleanly) before INIT ever sees it. *)
      fun var_names t = distinct (op =)
            (map #1 (Term.add_vars t []) @ map #1 (Term.add_tvars t []))
      fun shares (t1, t2) =
        exists (member (op =) (var_names t2)) (var_names t1)
      fun any_shared [] = false
        | any_shared (t :: ts) =
            exists (fn t' => shares (t, t')) ts orelse any_shared ts
  in if length prems < 2 orelse not (any_shared prems) then sequent
     else let
       fun give_up () = raise Agent_Give_Up ("technical_failure",
             "The goal has multiple subgoals sharing schematic variables \
             \and could not be merged into one.", zero_cost)
       val atomized =
         case SINGLE (ALLGOALS (My_Object_Logic.full_atomize_tac {strict=true} ctxt0)) sequent of
           SOME st => st
         | NONE => give_up ()
       (* Freeze schematics: Thm.assume rejects schematic hypotheses. *)
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


(* raw_AoA — the pure recording entry (§2.3): the gate, the three preprocessing
   segments, then the agent RPC.  NO store or cache logic anywhere in here.
   Synchronous: returns the four by-products (xcmds, cost, replay time, proof
   text) beside the theorem.  run_AoA feeds it to async_prove, which is where
   futures come into existence. *)
fun raw_AoA {driver, minilang_cfg, budget, invocation_id, task} (ctxt0, sequent0) =
  let open MessagePackBinIO.Pack MessagePackBinIO.Unpack Remote_Procedure_Calling
      (* THE GATE — first cell of the body (12.18). *)
      val () = if aoa_allowed () then () else gate_error (ctxt0, sequent0)
      val _ = Remote_Procedure_Calling.load ["IsaMini.AoA"]
      val cfg : cfg = (minilang_cfg, budget)
      val (task_kind, task_payload_packer) = pack_task task

      (* The three preprocessing segments, timed as one block: prep_elapsed is
         the entry's share of the recorded replay cost (D61 — what a replay
         will spend, not what this search spent). *)
      val ({elapsed = prep_elapsed, ...}, (sequent, split_script)) =
        Timing.timing (fn () =>
          let val st1 = standard_tac_segment ctxt0 sequent0
              val (st2, split_script) = Goal_Preprocess.preprocess_split_recorded ctxt0 st1
              val st3 = merge_segment ctxt0 st2
           in (st3, split_script) end) ()

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

      (* Configure context (D35 shared function; the 13th, conditional put
         stays here with the caller) *)
      val ctxt = configure_for_minilang ctxt0
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
        (* Third component: this op's ML-side execution time in ms (D61).
           The assembly verification replay sums it over the final op stream
           into assembled_isabelle_time. *)
        ret_schema = (fn (ctxt, msgs, flat_goal, elapsed_ms) =>
          packTuple3 (minilang_message_packer ctxt, minilang_flat_goal_packer ctxt, packInt)
                     (msgs, flat_goal, elapsed_ms)),
        function = (fn (from, to, opr) =>
          let val _ = Minilang.set_reporter listen_report
              val s0 = get_state from
              val result = Exn.capture (fn () =>
                let val (cfg', budget) = cfg
                    val mode = if !replay_mode then MiniLang_Agent.REPLAY
                               else MiniLang_Agent.LIVE
                    val full_config = (cfg', budget, counters, mode) : MiniLang_Agent.config
                    val ({elapsed, ...}, s1) =
                      Timing.timing (fn () => MiniLang_Agent.interpret full_config opr s0) ()
                    val ctxt' = Minilang.context_of s1
                    val msgs = clean_report ()
                    val _ = state := Symtab.update (to, s1) (!state)
                 in (ctxt', msgs, Minilang.leading_goal_data s1,
                     Time.toMilliseconds elapsed) end) ()
              (* Drain reporter messages on EVERY path: the success branch already
                 drained via clean_report, but a NOTICE pushed before a failure
                 (e.g. an Agent Hint notice fired during term checking) would
                 otherwise leak into the next op's report (A3). *)
              val _ = messages := []
           in Exn.release result
          end handle Minilang.OPR_FAIL (Minilang.PROOF_FAIL, msg) =>
              error (RPC_Pretty.trim_markup msg)
            | Minilang.OPR_FAIL (Minilang.INVALID_OPR, msg) =>
              error (RPC_Pretty.trim_markup msg)
            | Minilang.OPR_FAIL (Minilang.TERMLANG, msg) =>
              error (String.concat ["Syntax Error in Term Language.\n", RPC_Pretty.trim_markup msg])
            | Minilang.OPR_FAIL (Minilang.OTHER, msg) =>
              (* verbatim message: used e.g. by the Agent Hint Registry reject —
                 the term parsed fine, so no "Syntax Error" framing. *)
              error (RPC_Pretty.trim_markup msg)
            | MiniLang_Agent.FACT_IN_TIME_FAIL prop =>
              error (String.concat [
                "The following indicated fact is non-trivial, you must prove it manually:\n",
                RPC_Pretty.trim_markup (MiniLang_Agent.string_of_term (Minilang.context_of s0) prop)])
            | Phi_Sledgehammer_Solver.Auto_Fail _ =>
              error "Proof operation failed."
            | ERROR msg => error (RPC_Pretty.trim_markup msg)),
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
                    (* Collection entity: render name + up to 3 member props, with a
                       "... (N more)" sentinel when there are more.  dynamic_fact_members
                       returns NONE for a stale/non-collection (non-dynamic) name, which
                       drops this entity from the result. *)
                    let val full = Facts.intern facts name
                    in case Context_Callbacks.dynamic_fact_members (Context.Proof ctxt) facts full of
                         NONE => NONE
                       | SOME members =>
                           let val n = length members
                               val shown = map (SOT o Thm.prop_of) (take 3 members)
                               val props = if n > 3
                                           then shown @ ["... (" ^ string_of_int (n - 3) ^ " more)"]
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
              error (String.concat ["Bad operation: ", RPC_Pretty.trim_markup msg])),
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
        (* (state_id, whole): whole=false → leading subgoal only;
           whole=true → the whole goal sequent. *)
        arg_schema = unpackPair (unpackString, unpackBool),
        (* (term-vars, type-vars): each a list of (display-name, type-or-sort). *)
        ret_schema = packPair (packList (packPair (packString, packString)),
                               packList (packPair (packString, packString))),
        function = (fn (state_id, whole) =>
          let val s0 = get_state state_id
              val (vars, tvars) = Minilang.schematic_vars_of_goal whole s0
              val ctxt = Minilang.context_of s0
              val string_of_type = MiniLang_Agent.string_of_type ctxt
              val string_of_sort = MiniLang_Agent.string_of_sort ctxt
           in (map (fn (name_idx, ty) =>
                     (Term.string_of_vname name_idx, string_of_type ty)) vars,
               map (fn (name_idx, srt) =>
                     (Term.string_of_vname name_idx, string_of_sort srt)) tvars)
          end handle ERROR msg => error (String.concat ["Error: ", msg])),
        timeout = NONE
      }

      (* Gate prerun: execute `opr` on the state named by `state_id` WITHOUT
         recording the result into the state table, and return, for each
         derived subgoal, its schematic term/type variables.  The reporter is
         captured (not emitted) for the duration, so the Python side sees no
         protocol messages from the prerun; derived subgoals are discriminated
         structurally by Minilang.derived_subgoals_of.  Only sound for
         operations whose dispatch path does not advance session-shared
         counters — see the contract note on Minilang.derived_subgoals_of. *)
      val schematic_vars_of_derived_subgoals_callback = {
        name = "IsaMini.schematic_vars_of_derived_subgoals",
        (* (state_id, opr): opr in the same (cmd, arg) shape as proof_opr's. *)
        arg_schema = unpackPair (unpackString, MiniLang_Agent.xcmd_unpacker),
        (* per derived subgoal: (term-vars, type-vars), each a list of
           (display-name, type-or-sort) — same convention as
           IsaMini.schematic_variables_of. *)
        ret_schema = packList (packPair
          (packList (packPair (packString, packString)),
           packList (packPair (packString, packString)))),
        function = (fn (state_id, opr) =>
          let val s0 = get_state state_id
              val (cfg', budget) = cfg
              val mode = if !replay_mode then MiniLang_Agent.REPLAY
                         else MiniLang_Agent.LIVE
              val full_config = (cfg', budget, counters, mode) : MiniLang_Agent.config
              val (s1, prerun_msgs) =
                Minilang.record_reporter (MiniLang_Agent.interpret full_config opr) s0
              val subgoals = Minilang.derived_subgoals_of s0 s1 prerun_msgs
              val ctxt = Minilang.context_of s1
              val string_of_type = MiniLang_Agent.string_of_type ctxt
              val string_of_sort = MiniLang_Agent.string_of_sort ctxt
           in map (fn g =>
                (Term.add_vars g [] |> rev |> map (fn (xi, T) =>
                   (Term.string_of_vname xi, string_of_type T)),
                 Term.add_tvars g [] |> rev |> map (fn (xi, S) =>
                   (Term.string_of_vname xi, string_of_sort S))))
              subgoals
          end handle Minilang.OPR_FAIL (Minilang.PROOF_FAIL, msg) =>
              error (RPC_Pretty.trim_markup msg)
            | Minilang.OPR_FAIL (Minilang.INVALID_OPR, msg) =>
              error (RPC_Pretty.trim_markup msg)
            | Minilang.OPR_FAIL (Minilang.TERMLANG, msg) =>
              error (String.concat ["Syntax Error in Term Language.\n", RPC_Pretty.trim_markup msg])
            | Minilang.OPR_FAIL (Minilang.OTHER, msg) =>
              error (RPC_Pretty.trim_markup msg)
            | MiniLang_Agent.FACT_IN_TIME_FAIL prop =>
              error (String.concat [
                "The following indicated fact is non-trivial, you must prove it manually:\n",
                RPC_Pretty.trim_markup (MiniLang_Agent.string_of_term
                  (Minilang.context_of (get_state state_id)) prop)])
            | Phi_Sledgehammer_Solver.Auto_Fail _ =>
              error "Proof operation failed."
            | ERROR msg => error (RPC_Pretty.trim_markup msg)),
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
        ret_schema = packList (packTuple4 (packString, packString, packString, packBool)),
        function = (fn (state_id, terms) =>
          let val s0 = get_state state_id
              val ctxt = Minilang.context_of s0
              val SOT = MiniLang_Agent.string_of_term ctxt
              (* A candidate def is "conditional" if it carries a premise: a Pure ⟹
                 premise (Thm.nprems_of > 0) or a leading object-level ⟶ in the
                 conclusion. Unfold (Local_Defs.unfold_goals) only fires such a rule
                 when the premise is dischargeable from the goal's own premises;
                 otherwise it is a silent no-op, so the agent is warned (Python side). *)
              fun is_conditional_thm thm =
                Thm.nprems_of thm > 0 orelse
                (case Thm.concl_of thm of
                   @{const Trueprop} $ (Const (@{const_name HOL.implies}, _) $ _ $ _) => true
                 | Const (@{const_name HOL.implies}, _) $ _ $ _ => true
                 | _ => false)
              val facts = Proof_Context.facts_of ctxt
              (* Drop infrastructure / unciteable ("??.") definitions, mirroring
                 the filter applied to the semantic-search enumeration path. The
                 fact ref name may carry a "(i)" selector; strip it before the
                 name-based infra checks (the "??." extern test included). *)
              val {is_infra_thm, ...} = Infra_Filter.gen_infra_filters (Context.Proof ctxt)
              fun strip_sel s =
                case String.tokens (fn c => c = #"(") s of base :: _ => base | [] => s
              (* Terms of the leading goal — conclusion plus in-scope hypotheses
                 (Minilang's Intro moves premises out of the goal term into local
                 facts). Candidate definitions are kept only if their LHS matches
                 a subterm here. *)
              val ((_, goal_local_facts), goal_concl) =
                    Minilang.context_of_leading_goal (Minilang.print_state s0)
              val goal_terms = goal_concl :: map snd goal_local_facts
              val results = List.concat (map (fn term =>
                let val parsed_term = MiniLang_Agent.read_term ctxt term
                    val defs = Minilang.potential_defs_of ctxt (Term.head_of parsed_term) goal_terms
                 in defs
                    |> map_filter (fn (name, thm) =>
                         let val ext = Facts.extern ctxt facts name
                         in if String.isPrefix "??." ext
                               orelse is_infra_thm (strip_sel name, thm)
                            then NONE
                            else SOME (name, ext, SOT (Thm.prop_of thm), is_conditional_thm thm)
                         end)
                    (* Cap AFTER the infra / "??." filter, so the limit counts
                       citable defs (the ranking from potential_defs_of is
                       preserved by map_filter). *)
                    |> take 100
                end) terms)
              val (_, deduped) = fold (fn (q as (_, _, prop, _)) => fn (seen, acc) =>
                if member (op =) seen prop then (seen, acc)
                else (prop :: seen, acc @ [q])) results ([], [])
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
               (* Mirror pre_resolve_fact: allow schematic vars and fix them
                  before probing, so edit-time validation matches execution. *)
               let val prop = MiniLang_Agent.read_prop_schematic ctxt stmt
                   (* Same undeclared-free guard as check_extended_fact, so the
                      edit-time prefilter rejects what execution would reject. *)
                   val _ = MiniLang_Agent.reject_undeclared_frees
                             "Prove-in-time" "fact statement" s0 [prop]
                   val (props', inner) = Variable.import_terms true [prop] ctxt
                   val goal = Goal.init (Thm.cterm_of inner (hd props'))
               in case Seq.pull (Phi_Sledgehammer_Solver.fast_mepo_tac (Time.fromSeconds 3) inner 1 goal)
                    of SOME _ => NONE
                     | NONE => SOME "Proof failed"
               end
               catch ERROR msg => SOME (RPC_Pretty.trim_markup msg)
                   | Minilang.OPR_FAIL (_, msg) => SOME (RPC_Pretty.trim_markup msg)
                   | Timeout.TIMEOUT _ => SOME "Timed out"
                   | exn => SOME (RPC_Pretty.trim_markup (Runtime.exn_message exn))\<close>
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
              val raw_insts =
                map (fn (v, t) => ((Minilang_Aux.parse_var v, Position.none), t)) insts
          in
            (Rule_Insts.where_rule ctxt raw_insts [] raw_rule; NONE)
            handle ERROR msg => SOME msg
          end),
        timeout = NONE
      }

      (* Pre-flight validation for instantiating residual schematic
       * variables in the WHOLE goal AFTER a rule/case-split/induction has
       * been applied. Takes one round of (var-name, value-string) pairs and
       * applies it to the current (post-rule) goal state via the same
       * 2-phase primitive used on replay. Returns NONE on success, or
       * SOME error_msg on any failure (malformed name, unknown/non-goal
       * variable, type/sort clash) — turned into a clean BadAnswer on the
       * Python side. *)
      val validate_inst_var_callback = {
        name = "IsaMini.validate_inst_var",
        arg_schema = unpackPair (unpackString,
                       unpackList (unpackPair (unpackString, unpackString))),
        ret_schema = packOption packString,
        function = (fn (state_id, round) =>
          let val s0 = get_state state_id
          in \<^try>\<open>(MiniLang_Agent.apply_post_insts [round] s0; NONE)
               catch ERROR msg => SOME (RPC_Pretty.trim_markup msg)
                   | exn => SOME (RPC_Pretty.trim_markup (Runtime.exn_message exn))\<close>
          end),
        timeout = NONE
      }

      (* Build AoA command with local callbacks.  No hashing and no store access
         in here (D59): the key lives in the caching layer (run_AoA /
         hammer_or_AoA), computed on the goal BEFORE preprocessing. *)
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
                val enable_write_memory = Config.get ctxt AoA_enable_write_memory
            in packTuple10 (context_packer ctxt, minilang_flat_goal_packer ctxt,
                           packString, packString, packString, packString, packString,
                           packTuple3 (packInt, packInt, packInt),
                           packPair (packString, fn () => task_payload_packer),
                           packBool)
                          (global_context, s0_flat_goal, driver, log_dir, invocation_id,
                           retrieval_forking, interactive_retrieval,
                           (#timeout_seconds budget, #max_tool_calls budget, #max_retries budget),
                           (task_kind, ()), enable_write_memory)
            end),
        (* Stats tuple: the 10th element is assembled_isabelle_time in ms (D61) —
           the per-op ML execution times summed over the assembly verification
           replay of the final op stream.  It is NOT part of agent_cost; raw_AoA
           folds it into the replay-time by-product right below.  No blob comes
           back over this wire: raw_AoA assembles the blob itself from the
           returned op stream (D41 — the blob never leaves the
           raw_AoA/aoa_replay codec pair). *)
        ret_schema = unpackTuple5 (unpackList MiniLang_Agent.xcmd_unpacker,
                                   unpackOption unpackString,
                                   (fn src => let val ((i,cw,cr,o_,c,tc,it,mt,qwt,ait), src') =
                                      unpackTuple10 (unpackInt,unpackInt,unpackInt,unpackInt,unpackReal,unpackInt,unpackReal,unpackReal,unpackReal,unpackInt) src
                                    in (({input=i,cache_write=cw,cache_read=cr,output=o_,cost=c,tool_calls=tc,isabelle_time=it,model_time=mt,quota_wait_time=qwt}, ait), src') end),
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
          mk_callback schematic_vars_of_derived_subgoals_callback,
          mk_callback goal_variables_callback,
          mk_callback potential_defs_callback,
          mk_callback abbreviation_defs_callback,
          mk_callback analyze_induct_callback,
          mk_callback analyze_case_split_callback,
          mk_callback validate_instantiation_callback,
          mk_callback validate_inst_var_callback,
          mk_callback contextual_thms_callback,
          mk_callback fact_propositions_callback,
          mk_callback validate_prove_in_time_callback,
          mk_callback check_looping_rules_callback,
          Universal_Key.make_universal_key_callback' (SOME thm_cache) au,
          Universal_Key.make_key_of_theorems_callback' (SOME thm_cache) au,
          Config.make_config_lookup_callback au,
          constants, theorems, types, classes, locales, named_theorems, methods,
          introduction_rules, elimination_rules,
          induction_rules, case_split_rules,
          Context_Callbacks.make_theory_long_name_callback au,
          Context_Callbacks.make_experience_constituents_callback au,
          Context_Callbacks.make_experiences_callback au,
          Context_Callbacks.make_loaded_theory_hashes_callback au,
          Semantic_Store.make_interpret_theory_callback au
        ]
      }

      val timer = Timer.startRealTimer ()
      val (xcmds, s1o,
           ({input, cache_write, cache_read, output, cost, tool_calls, isabelle_time, model_time, quota_wait_time},
            assembled_isabelle_time_ms),
           reason, detail) =
            call_command aoa_cmd (global_context, driver, invocation_id)
      val elapsed = Timer.checkRealTimer timer
      val agent_cost : agent_cost =
        {input=input, cache_write=cache_write, cache_read=cache_read, output=output,
         cost=cost, tool_calls=tool_calls, isabelle_time=isabelle_time, model_time=model_time,
         quota_wait_time=quota_wait_time}
      (* tracing, per the §6.2 channel table (round-3 review PC-2, author ruling a) *)
      val _ = tracing (string_of_cost agent_cost ^ " time=" ^ Time.toString elapsed ^ "s")
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
           ; let (* D41: raw_AoA itself assembles the blob — the split script
                    never left this function, and Python already handed the
                    final op stream back in the return value.  The blob is the
                    internal secret of exactly this assembler and the
                    aoa_replay decoder. *)
                 val prf_text =
                   let val buf = BytesIO.mkOutstream ()
                       val () = MessagePackBytesIO.Pack.packPair
                                  (MessagePackBytesIO.Pack.packString,
                                   MessagePackBytesIO.Pack.packList MiniLang_Agent.xcmd_packer_bytes)
                                  (split_script, xcmds) buf
                       val b64 = BytesIO.toString buf |> Bytes.string
                                 |> Base64.encode |> Bytes.content
                    in "aoa_replay " ^ quote b64 end
                 (* D61: what a REPLAY of this proof will cost — entry
                    preprocessing plus the final op stream's summed ML execution
                    time (measured over the assembly verification replay).  LLM
                    round-trips, RPC overhead and dead branches are deliberately
                    not in it.  Raw (undivided) time: the write layer divides
                    by Timeout.scale. *)
                 val replay_time =
                   prep_elapsed + Time.fromMilliseconds assembled_isabelle_time_ms
              in ((xcmds, agent_cost, replay_time, prf_text),
                  Minilang.conclude ctxt s1')
             end
         end
        else error "Internal Error: the proof state returned by the Agent is not finished"
    | NONE => error "Internal Error: the state returned by the Agent is not found"
  ) | NONE =>
        (case reason
          of SOME r => raise Agent_Give_Up (r, the_default "" detail, agent_cost)
           | NONE => error "Agent gives up (protocol error: missing reason)")
  end

(*** run_AoA — the caching wrapper: [read_store -> level-0 lookup] ->
     raw_AoA -> [write_store -> write-back].  No gate here (it sits in
     raw_AoA's entry). ***)

fun run_AoA {driver, minilang_cfg, budget, invocation_id,
             read_store, write_store, async, task} (ctxt, sequent) =
  let val read  = case read_store  of SOME b => b | NONE => Config.get ctxt AoA_read_proof_store
      val write = case write_store of SOME b => b | NONE => Config.get ctxt AoA_write_proof_store
      (* One call, one key (D59): the all-goals key of the ORIGINAL,
         pre-preprocessing goal — the split race must not move the key. *)
      val key = Hasher.all_goals (ctxt, sequent)
   in case (if read
            then Proof_Store_AoA.store_hit_replay {key = key, write_store = write} (ctxt, sequent)
            else NONE) of
        SOME (std_time, prf_text, sequent') =>
          (* Level-0 hit: the agent never ran — [] and zero_cost are statements
             of fact, not placeholders (§2.3).  The recorded standard-machine
             time is scaled back to this machine's clock; the stored text goes
             out verbatim (the blob never leaves the aoa_replay codec pair). *)
          (Future.value ([], zero_cost, Time.scale (Timeout.scale ()) std_time, prf_text),
           sequent')
      | NONE =>
          let val (_, futs, sequent') =
                Phi_Sledgehammer_Solver.async_prove async Phi_Sledgehammer_Solver.All_At_Once
                  (raw_AoA {driver = driver, minilang_cfg = minilang_cfg, budget = budget,
                            invocation_id = invocation_id, task = task})
                  (ctxt, sequent)
           in case futs of
                [fut] =>
                  let (* The write-back rides as a DEPENDENT task on the product
                        future (§2.5): the sync state joins a fulfilled
                        Future.value, the async state wakes after the fork —
                        one piece of code for both.  This join is the
                        sanctioned store-write exception to the no-join rule.
                        interrupts = true (stage-0 ruling on store-write forks):
                        the body takes the .proof-store fcntl lock, and
                        with_file_lock's `run` restores the attributes in effect
                        at task entry — forked uninterruptible, the blocking
                        setlkw wait (and the timeout-less L1 RPC) could never
                        be cancelled. *)
                      val _ =
                        if write then
                          ignore ((singleton o Future.forks)
                            {name = "run_AoA_store_write", group = NONE,
                             deps = [Future.task_of fut], pri = ~1, interrupts = true}
                            (fn () =>
                               case Exn.capture Future.join fut of
                                 Exn.Res (_, _, replay_time, prf_text) =>
                                   let val thy = Proof_Context.theory_of ctxt
                                       val std = Phi_Proof_Store.standard_time replay_time
                                    in Phi_Proof_Store.update_cached_proof thy (key, (std, prf_text))
                                     ; Proof_Store_AoA.l1_write (key, std, prf_text)
                                   end
                               | Exn.Exn _ => () (*no proof came out: nothing to write*)))
                        else ()
                   in (fut, sequent') end
              | _ =>
                  (* async_prove's zero-subgoal short circuit: nothing to prove,
                     nothing ran, nothing is written. *)
                  (Future.value ([], zero_cost, Time.zeroTime, ""), sequent')
          end
  end


(*** aoa_replay — the pure-ML decoder half of the blob codec (§2.7).  The
     method itself is registered in Minilang_AoA.thy (D39); this is its body.
     Failure is METHOD failure (an empty result sequence), so eval_prf_str's
     caller reads it as "cached proof no longer works". ***)

(* Execute the recorded split script (D41): a method text applied to the whole
   state — replaces the recording-side race, never re-runs it. *)
fun exec_split_script ctxt script st =
  let val kws = Keyword.no_major_keywords
                  (Thy_Header.get_keywords (Proof_Context.theory_of ctxt))
      val seq =
        Method.evaluate
          (Parse.read_embedded ctxt kws (Method.parser 0) (Input.string script)
             |> fst |> Method.check_text ctxt)
          ctxt [] (ctxt, st)
   in case Position.setmp_thread_data Position.none Seq.pull seq of
        SOME (Seq.Result (_, st'), _) => st'
      | _ => error ("aoa_replay: the recorded split script failed: " ^ script)
  end

fun aoa_replay_method b64 _ (*using*) (ctxt, sequent) = Seq.make (fn () => \<^try>\<open>
  let (* 0: decode blob = base64(msgpack((script, xcmd list))) (D30/D31) *)
      val ((script, ops), _) =
        b64 |> Bytes.string |> Base64.decode |> Bytes.content
            |> BytesIO.fromString
            |> MessagePackBytesIO.Unpack.unpackPair
                 (MessagePackBytesIO.Unpack.unpackString,
                  MessagePackBytesIO.Unpack.unpackList MiniLang_Agent.xcmd_unpacker_bytes)
      (* 1-3: replay order mirrors the recording order (D64): deterministic
         segments re-run in place, the split segment runs the recorded script. *)
      val st1 = standard_tac_segment ctxt sequent
      val st2 = if script = "" then st1 else exec_split_script ctxt script st1
      val st3 = merge_segment ctxt st2
      (* 4-6 *)
      val ctxt' = configure_for_minilang ctxt
      val s0 = Minilang.INIT ctxt' st3
      val counters = {prem_counter = Synchronized.var "prem_counter" 0}
                       : MiniLang_Agent.counters
      val _ = Minilang.set_reporter (K ())
      val (dcfg, dbudget) = MiniLang_Agent.default_cfg
      val config = (dcfg, dbudget, counters, MiniLang_Agent.REPLAY)
                     : MiniLang_Agent.config
      val s1 = fold (MiniLang_Agent.interpret config) ops s0
      (* 7 *)
      val th = Minilang.conclude ctxt' s1
   in SOME (Seq.Result (ctxt, th), Seq.empty) end
  catch exn =>
    (tracing ("[aoa_replay] replay failed: " ^ Runtime.exn_message exn); NONE)\<close>)


(*** The tactic ***)

fun is_dummy th =
  let fun chk (Const(\<^const_name>\<open>Pure.term\<close>, _) $ _) = true
        | chk (Const(\<^const_name>\<open>Pure.prop\<close>, _) $ X) = chk X
        | chk _ = false
   in Thm.is_dummy th orelse chk (Thm.prop_of th)
  end

(* `by aoa` ≈ run_AoA (§2.3); always async = false. *)
fun method _ (*using*) (ctxt, sequent) = Seq.make (fn () =>
  if is_dummy sequent then NONE
  else let val driver = Config.get ctxt aoa_driver
           val invocation_id = make_invocation_id ()
           val log_dir = Config.get ctxt AoA_log_dir
           val log_path = if log_dir = "" then "(no logging)"
                          else log_dir ^ "/" ^ invocation_id
           val _ = writeln ("AoA (driver: " ^ driver ^ ", logs: " ^ log_path ^ ")")
           val (agent_cfg, budget) = MiniLang_Agent.default_cfg
        in run_AoA {driver = driver, minilang_cfg = agent_cfg, budget = budget,
                    invocation_id = invocation_id, read_store = NONE, write_store = NONE,
                    async = false, task = Usual} (ctxt, sequent)
           |> (fn (_, sequent') => SOME (Seq.Result (ctxt, sequent'), Seq.empty))
           handle Agent_Give_Up (reason, detail, _) =>
             error (banner_of reason ^ "\n" ^ detail)
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
