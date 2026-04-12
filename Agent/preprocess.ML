(*  Title:  Agent/preprocess.ML
    Author: Qiyuan Xu (with AI assistance)

Preprocessing tactic for large proof goals. Structurally splits conjunctions,
implications, and universal quantifiers into smaller subgoals before the agent
handles each piece.
*)

signature GOAL_PREPROCESS = sig
  val split_skip_size : int
  val preprocess_size_threshold : int
  val custom_split_tac : Proof.context -> int -> tactic
  val preprocess_split_tac : Proof.context -> tactic
end

structure Goal_Preprocess : GOAL_PREPROCESS = struct

(* Subgoal conclusions smaller than this are left unsplit *)
val split_skip_size = 30

(* preprocess_split_tac only triggers when the largest subgoal exceeds this *)
val preprocess_size_threshold = 200

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

fun preprocess_split_tac ctxt st =
  let
    val max_goal_size = fold (fn p => fn mx =>
        Int.max (Infra_Filter.smart_size_of_term p, mx))
      (Thm.prems_of st) 0
  in
    if max_goal_size <= preprocess_size_threshold then Seq.single st
    else
      let
        val _ = writeln ("Max subgoal size " ^
                  string_of_int max_goal_size ^ " > " ^
                  string_of_int preprocess_size_threshold ^
                  ", preprocessing by splitting...")
        val timeout = Time.fromSeconds 8
      in
        (* Step 1: try auto with 8-second timeout *)
        (case try_tac_timeout timeout (Clasimp.auto_tac (Smart_Split.add_smart_split ctxt)) st of
          SOME st' =>
            (writeln "auto succeeded in preprocessing";
             Seq.single st')
        | NONE =>
          let
            val _ = writeln "auto timed out or failed, trying clarsimp..."
            (* Step 2: try clarsimp, then custom split *)
            val st' =
              (case try_tac_timeout timeout
                      (ALLGOALS (Clasimp.clarsimp_tac (Smart_Split.add_smart_split ctxt))) st of
                SOME s =>
                  (writeln "clarsimp succeeded, applying custom split..."; s)
              | NONE =>
                  (writeln "clarsimp timed out, applying custom split \
                           \on original goal..."; st))
          in
            (* Step 3: custom split on whatever state we have *)
            ALLGOALS (custom_split_tac ctxt) st'
          end)
      end
  end

end
