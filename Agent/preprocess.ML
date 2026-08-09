(*  Title:  Agent/preprocess.ML
    Author: Qiyuan Xu (with AI assistance)

Preprocessing tactic for large proof goals. Structurally splits conjunctions,
implications, and universal quantifiers into smaller subgoals before the agent
handles each piece.
*)

(* AoA's master debug switch: whether the agent behaves in a way that suits
   diagnosing a run rather than serving one.
   false (default) — the `aoa` method stays quiet about its own bookkeeping.
   true            — enable via `declare [[AoA_Debug]]` when diagnosing a run.
   NOT limited to the ML-side progress chatter below: it is the general "I am
   debugging AoA" flag, and is registered for RPC lookup so the Python side can
   consult it too (Config.lookup "AoA_Debug", see Isabelle_RPC/Tools/config.ML).
   Declared here rather than in agent_server.ML because preprocess.ML is loaded
   FIRST (see Minilang_AoA.thy), so a declaration there would be invisible to
   the sites below. *)
val AoA_Debug = Attrib.setup_config_bool \<^binding>\<open>AoA_Debug\<close> (K false);
val _ = Config.register_rpc_option "AoA_Debug" (Config.bool_value AoA_Debug);

signature GOAL_PREPROCESS = sig
  val split_skip_size : int
  val preprocess_size_threshold : int
  val custom_split_tac : Proof.context -> int -> tactic
  val preprocess_split_tac : Proof.context -> tactic

  (* The split segment is a timed race (auto / clarsimp+custom / custom), so its
     outcome depends on machine load.  Recording therefore keeps the transformed
     state TOGETHER with a method text describing the transformation actually
     performed (D41); replay executes that text instead of re-racing.  "" means
     the segment did nothing.  The texts are compositions of the three
     aoa_split_* methods registered below. *)
  val preprocess_split_recorded : Proof.context -> thm -> thm * string

  (* Reporter message carrying the recorded split script to Python, which puts
     it into the blob's first component (D30/D41). *)
  exception SPLIT_SCRIPT of string
end

structure Goal_Preprocess : GOAL_PREPROCESS = struct

exception SPLIT_SCRIPT of string

(* Progress chatter, gated on AoA_Debug *)
fun dbg ctxt msg = if Config.get ctxt AoA_Debug then writeln msg else ()

(* Subgoal conclusions smaller than this are left unsplit *)
val split_skip_size = 30

(* preprocess_split_tac only triggers when the largest subgoal exceeds this *)
val preprocess_size_threshold = 480

(** Custom recursive split tactic **)

(* Recursively split a single subgoal by its leading connective.
   Skips goals whose HOL-level conclusion is smaller than split_skip_size. *)
fun custom_split_tac ctxt = SUBGOAL (fn (goal, i) =>
  let
    val concl = Logic.strip_assums_concl goal
    val obj_concl =
      (case concl of
        Const(\<^const_name>\<open>Trueprop\<close>, _) $ t => t
      | t => t)
    val size = Infra_Filter.smart_size_of_term obj_concl
  in
    if size < split_skip_size then all_tac
    else
      (case Term.head_of obj_concl of
        Const(\<^const_name>\<open>HOL.conj\<close>, _) =>
          resolve_tac ctxt @{thms conjI} i
          THEN custom_split_tac ctxt (i + 1)
          THEN custom_split_tac ctxt i
      | Const(\<^const_name>\<open>HOL.implies\<close>, _) =>
          resolve_tac ctxt @{thms impI} i
          THEN custom_split_tac ctxt i
      | Const(\<^const_name>\<open>HOL.All\<close>, _) =>
          resolve_tac ctxt @{thms allI} i
          THEN custom_split_tac ctxt i
      | _ => all_tac)
  end)


(** Main preprocessing tactic **)

(* Try a tactic with a timeout, returning SOME st' on success, NONE on
   timeout or failure. *)
fun try_tac_timeout time tac st =
  Timeout.apply time (fn () => SINGLE tac st) ()
  handle Timeout.TIMEOUT _ => NONE
       | Exn.Interrupt_Breakdown => NONE

(* The race itself, shared by the tactic and the recording entry. *)
datatype split_outcome =
    NO_SPLIT                       (*largest subgoal below the threshold*)
  | AUTO_WON of thm
  | CUSTOM of thm Seq.seq * bool   (*after custom split; bool = clarsimp preceded*)

fun split_race ctxt st =
  let
    val max_goal_size = fold (fn p => fn mx =>
        Int.max (Infra_Filter.smart_size_of_term p, mx))
      (Thm.prems_of st) 0
  in
    if max_goal_size <= preprocess_size_threshold then NO_SPLIT
    else
      let
        val _ = dbg ctxt ("Max subgoal size " ^
                  string_of_int max_goal_size ^ " > " ^
                  string_of_int preprocess_size_threshold ^
                  ", preprocessing by splitting...")
        val timeout = Time.fromSeconds 8
      in
        (* Step 1: try auto with 8-second timeout *)
        (case try_tac_timeout timeout (Clasimp.auto_tac (Smart_Split.add_smart_split ctxt)) st of
          SOME st' =>
            (dbg ctxt "auto succeeded in preprocessing";
             AUTO_WON st')
        | NONE =>
          let
            val _ = dbg ctxt "auto timed out or failed, trying clarsimp..."
            (* Step 2: try clarsimp, then custom split *)
            val (st', clarsimped) =
              (case try_tac_timeout timeout
                      (ALLGOALS (Clasimp.clarsimp_tac (Smart_Split.add_smart_split ctxt))) st of
                SOME s =>
                  (dbg ctxt "clarsimp succeeded, applying custom split..."; (s, true))
              | NONE =>
                  (dbg ctxt "clarsimp timed out, applying custom split \
                            \on original goal..."; (st, false)))
          in
            (* Step 3: custom split on whatever state we have *)
            CUSTOM (ALLGOALS (custom_split_tac ctxt) st', clarsimped)
          end)
      end
  end

fun preprocess_split_tac ctxt st =
  case split_race ctxt st of
    NO_SPLIT => Seq.single st
  | AUTO_WON st' => Seq.single st'
  | CUSTOM (seq, _) => seq

(* Method texts below are compositions of the aoa_split_* methods, which are
   registered as the LITERAL recording tactics — each text replays exactly the
   transformation of its branch (R22).  A branch that changed nothing renders
   "" so replay skips the segment instead of re-running a no-op. *)
fun preprocess_split_recorded ctxt st =
  case split_race ctxt st of
    NO_SPLIT => (st, "")
  | AUTO_WON st' =>
      if Thm.eq_thm_prop (st, st') then (st', "") else (st', "aoa_split_auto")
  | CUSTOM (seq, clarsimped) =>
      (case Seq.pull seq of
         SOME (st'', _) =>
           (st'', if clarsimped then "(aoa_split_clarsimp, aoa_split_custom)"
                  else "aoa_split_custom")
       | NONE => (st, ""))   (*whole segment failed: the caller keeps the original state*)

(* Replay-facing methods (D41): each is byte-for-byte one branch's tactic.
   Do NOT reuse auto_sledgehammer's `auto_split` / `clarsimp_split` — those wrap
   CHANGED_PROP resp. operate on the first subgoal only, which is not what the
   recording ran. *)
val _ = Theory.setup
  (Method.setup \<^binding>\<open>aoa_split_auto\<close>
    (Scan.succeed (fn ctxt =>
      SIMPLE_METHOD (Clasimp.auto_tac (Smart_Split.add_smart_split ctxt))))
    "replay of the split segment's auto branch" #>
   Method.setup \<^binding>\<open>aoa_split_clarsimp\<close>
    (Scan.succeed (fn ctxt =>
      SIMPLE_METHOD (ALLGOALS (Clasimp.clarsimp_tac (Smart_Split.add_smart_split ctxt)))))
    "replay of the split segment's clarsimp step" #>
   Method.setup \<^binding>\<open>aoa_split_custom\<close>
    (Scan.succeed (fn ctxt =>
      SIMPLE_METHOD (ALLGOALS (custom_split_tac ctxt))))
    "replay of the split segment's custom split step")

end
