(*  Title:  Agent/proof_store_AoA.ML
    Author: Qiyuan Xu (with AI assistance)

The AoA side of the proof store (§2.1): the three L1 RPCs (lookup / store /
invalidate, served by the Python module IsaMini.proof_store, one SQLite
wrapper — NOT the agent stack) and the level-0 lookup brick
`store_hit_replay`, which run_AoA (and, later, hammer_or_AoA) call before any
search.  Loaded by Minilang_AoA.thy BEFORE agent_server.ML.

L1 and L2 use the same key (the all-goals hash of the goal before any
preprocessing) and the same value shape (standard-machine times, proof text);
on the wire the times are (cpu_ms, wall_ms) nested in one slot.
Every RPC here degrades silently on failure — a downstream user may have no
Python at all, and an obligation must never die of that.  None of these RPCs
may touch the semantic DB; that holds by construction, the Python module does
not import the agent stack.
*)

signature PROOF_STORE_AoA = sig

  (* L1 query RPC: SOME (standard-machine times, proof text) on a hit; a MISS
     and ANY failure (no Python, no module, dead host) both return NONE. *)
  val l1_lookup : Phi_Proof_Store.proof_id -> (Phi_Proof_Store.times * string) option

  (* L1 write RPC, paired with the query.  Failures are swallowed silently. *)
  val l1_write : Phi_Proof_Store.proof_id * Phi_Proof_Store.times * string -> unit

  (* L1 invalidation RPC: deletes the row after a hit whose replay failed —
     the L1 mirror of the L2 tombstone.  Failures are swallowed silently. *)
  val l1_invalidate : Phi_Proof_Store.proof_id -> unit

  (* Level 0 (§2.3): the lookup-and-replay brick, every level before any
     search and outside any fork.  Three levels, in order:
       1. L2 by proof id.  A hit that fails to replay is tombstoned
          (invalidate_proof_cache) and the lookup falls through.
       2. L2 by goal hash (skipped when no hash is given).  A hit that replays
          is promoted: written to L2 under `key` with that hash (gated by
          write_store; L2 only, never L1).  One that fails is forgotten in
          memory only (invalidate_proof_cache_by_hash: no frame) and the
          lookup falls through.
       3. L1 by proof id.  A hit that replays while L2 is cold is upgraded
          into an L2 entry (gated by write_store); one that fails is
          invalidated (l1_invalidate) and the result is a miss.
     Across all three: a record that already failed under an earlier level --
     same times, same text -- is not replayed again but counted as failed
     outright.  Invalidations are store maintenance and are NOT gated.
     Every level returns (standard-machine times, text) and replays through
     the one generic channel eval_prf_str; a text of the form `aoa_replay "…"`
     enters the pure-ML §2.7 flow through that method, never through a second
     path.  The hash is computed by the caller: this brick holds no key recipe.
     Do not wrap another timeout around this: the replay limits are
     replay_limits of the recorded std_time, applied inside eval_prf_str. *)
  val store_hit_replay : {key: Phi_Proof_Store.proof_id, hash: Hasher.digest option, write_store: bool}
                      -> Proof.context * thm
                      -> (Phi_Proof_Store.times * string * thm) option

end

structure Proof_Store_AoA : PROOF_STORE_AoA = struct

local open MessagePackBinIO.Pack MessagePackBinIO.Unpack in

fun l1_lookup key =
  \<^try>\<open>
    let val _ = Remote_Procedure_Calling.load ["IsaMini.proof_store"]
        val cmd : (string, ((int * int) * string) option) Remote_Procedure_Calling.command = {
              name = "IsaMini.ProofStore.lookup",
              arg_schema = packString,
              ret_schema = unpackOption (unpackPair (unpackPair (unpackInt, unpackInt), unpackString)),
              callback = [],
              timeout = NONE }
     in Remote_Procedure_Calling.call_command cmd key
        |> Option.map (apfst Phi_Proof_Store.times_of_ms)
    end
  catch _ => NONE\<close>

fun l1_write (key, std_time, text) =
  \<^try>\<open>
    let val _ = Remote_Procedure_Calling.load ["IsaMini.proof_store"]
        val cmd : (string * (int * int) * string, unit) Remote_Procedure_Calling.command = {
              name = "IsaMini.ProofStore.store",
              arg_schema = packTuple3 (packString, packPair (packInt, packInt), packString),
              ret_schema = unpackUnit,
              callback = [],
              timeout = NONE }
     in Remote_Procedure_Calling.call_command cmd
          (key, Phi_Proof_Store.ms_of_times std_time, text)
    end
  catch _ => ()\<close>

fun l1_invalidate key =
  ((*the L1 counterpart of L2's report_cache_is_outdated: the one countable signal
     for cross-family stale hits (UNIFIED_KEY_MINT_PLAN §5.7) -- keep the "L1" prefix,
     counting must separate the two ledgers*)
   warning ("L1 proof cache " ^ quote key ^ " is outdated!");
   \<^try>\<open>
    let val _ = Remote_Procedure_Calling.load ["IsaMini.proof_store"]
        val cmd : (string, unit) Remote_Procedure_Calling.command = {
              name = "IsaMini.ProofStore.invalidate",
              arg_schema = packString,
              ret_schema = unpackUnit,
              callback = [],
              timeout = NONE }
     in Remote_Procedure_Calling.call_command cmd key
    end
  catch _ => ()\<close>)

end (*local*)

fun store_hit_replay {key, hash, write_store} (ctxt, sequent) =
  let val thy = Proof_Context.theory_of ctxt
      val kws = Keyword.no_major_keywords (Thy_Header.get_keywords thy)
      val n = Thm.nprems_of sequent
      (* SOME th on success; NONE only on Auto_Fail (eval_prf_str's whole
         failure vocabulary) — anything else is a bug and must escape.
         Capture site (EVENT_LOG_PLAN 7): anything escaping the replay —
         including a traceless Interrupt_Breakdown record — is logged before
         it is re-raised unchanged; Auto_Fail is the ordinary miss and is
         excluded from the record predicate.  The region is bounded by the
         replay_limits applied inside eval_prf_str. *)
      fun replay (std_time, prf_text) =
        (case Exn.capture_body (fn () =>
                Exception_Log.capture
                  {site = "store replay",
                   record = fn Phi_Sledgehammer_Solver.Auto_Fail _ => false
                             | e => Exception_Log.default_record e}
                  (fn () =>
                    Phi_Sledgehammer_Solver.eval_prf_str kws n
                      (Phi_Proof_Store.replay_limits std_time) prf_text (ctxt, sequent)
                    |> (fn (_, (_, th)) => th))) of
           Exn.Res th => SOME th
         | Exn.Exn (Phi_Sledgehammer_Solver.Auto_Fail _) => NONE
         | Exn.Exn exn => Exn.reraise exn)
      (* `failed` holds the records earlier levels gave up on: one of them met
         again is a failure without another replay. *)
      fun replay_unless failed (s as (std_time, prf_text)) =
        if member (op =) failed s then NONE
        else Option.map (fn th => (std_time, prf_text, th)) (replay s)
      (* L2 is cold under `key` on every route that writes here (miss, or
         hit-then-tombstone): write the row as-is -- same times, same text. *)
      fun write_l2 (std_time, prf_text, _) =
        if write_store
        then Phi_Proof_Store.update_cached_proof thy {id = key, hash = hash} (std_time, prf_text)
        else ()
      fun try_l1 failed =
        case l1_lookup key of
          NONE => NONE
        | SOME s =>
            (case replay_unless failed s of
               SOME hit => (write_l2 hit; SOME hit)
             | NONE => (l1_invalidate key; NONE))
      fun try_hash failed =
        case hash of
          NONE => try_l1 failed
        | SOME h =>
            case Phi_Proof_Store.get_cached_proof_by_hash thy h of
              NONE => try_l1 failed
            | SOME s =>
                (case replay_unless failed s of
                   SOME hit => (write_l2 hit; SOME hit)   (*promotion*)
                 | NONE =>
                     (* ruling I: the hash entry is forgotten, no frame is written *)
                     (Phi_Proof_Store.invalidate_proof_cache_by_hash h thy;
                      try_l1 (s :: failed)))
   in case Phi_Proof_Store.get_cached_proof thy key of
        NONE => try_hash []
      | SOME s =>
          (case replay_unless [] s of
             SOME hit => SOME hit   (*L2 hit: zero write-back*)
           | NONE =>
               (Phi_Proof_Store.invalidate_proof_cache true key thy;
                try_hash [s]))
  end

end
