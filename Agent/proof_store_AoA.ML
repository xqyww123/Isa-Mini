(*  Title:  Agent/proof_store_AoA.ML
    Author: Qiyuan Xu (with AI assistance)

The AoA side of the proof store (§2.1): the three L1 RPCs (lookup / store /
invalidate, served by the Python module IsaMini.proof_store, one SQLite
wrapper — NOT the agent stack) and the level-0 lookup brick
`store_hit_replay`, which run_AoA (and, later, hammer_or_AoA) call before any
search.  Loaded by Minilang_AoA.thy BEFORE agent_server.ML.

L1 and L2 use the same key (the all-goals hash of the goal before any
preprocessing) and the same value shape (standard-machine time, proof text).
Every RPC here degrades silently on failure — a downstream user may have no
Python at all, and an obligation must never die of that.  None of these RPCs
may touch the semantic DB; that holds by construction, the Python module does
not import the agent stack.
*)

signature PROOF_STORE_AoA = sig

  (* L1 query RPC: SOME (standard-machine time, proof text) on a hit; a MISS
     and ANY failure (no Python, no module, dead host) both return NONE. *)
  val l1_lookup : Hasher.digest -> (Time.time * string) option

  (* L1 write RPC, paired with the query.  Failures are swallowed silently. *)
  val l1_write : Hasher.digest * Time.time * string -> unit

  (* L1 invalidation RPC: deletes the row after a hit whose replay failed —
     the L1 mirror of the L2 tombstone.  Failures are swallowed silently. *)
  val l1_invalidate : Hasher.digest -> unit

  (* Level 0 (§2.3): the two-level lookup-and-replay brick, both levels before
     any search and outside any fork.  Both levels return (std_time, text) and
     both replay through the one generic channel eval_prf_str; a text of the
     form `aoa_replay "…"` enters the pure-ML §2.7 flow through that method,
     never through a second path.  L2 replay failure writes a tombstone and
     falls to L1; L1 replay failure invalidates the row and reports a miss;
     an L1 hit that replays while L2 is cold is upgraded into an L2 entry
     (gated by write_store — invalidations are store maintenance and are NOT
     gated).  Do not wrap another Timeout.apply around this: the replay budget
     is tolerant_time of the recorded std_time, applied inside eval_prf_str. *)
  val store_hit_replay : {key: Hasher.digest, write_store: bool}
                      -> Proof.context * thm
                      -> (Time.time * string * thm) option

end

structure Proof_Store_AoA : PROOF_STORE_AoA = struct

local open MessagePackBinIO.Pack MessagePackBinIO.Unpack in

fun l1_lookup key =
  \<^try>\<open>
    let val _ = Remote_Procedure_Calling.load ["IsaMini.proof_store"]
        val cmd : (string, (int * string) option) Remote_Procedure_Calling.command = {
              name = "IsaMini.ProofStore.lookup",
              arg_schema = packString,
              ret_schema = unpackOption (unpackPair (unpackInt, unpackString)),
              callback = [],
              timeout = NONE }
     in case Remote_Procedure_Calling.call_command cmd key of
          SOME (ms, text) => SOME (Time.fromMilliseconds ms, text)
        | NONE => NONE
    end
  catch _ => NONE\<close>

fun l1_write (key, std_time, text) =
  \<^try>\<open>
    let val _ = Remote_Procedure_Calling.load ["IsaMini.proof_store"]
        val cmd : (string * int * string, unit) Remote_Procedure_Calling.command = {
              name = "IsaMini.ProofStore.store",
              arg_schema = packTuple3 (packString, packInt, packString),
              ret_schema = unpackUnit,
              callback = [],
              timeout = NONE }
     in Remote_Procedure_Calling.call_command cmd
          (key, Time.toMilliseconds std_time, text)
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

fun store_hit_replay {key, write_store} (ctxt, sequent) =
  let val thy = Proof_Context.theory_of ctxt
      val kws = Keyword.no_major_keywords (Thy_Header.get_keywords thy)
      val n = Thm.nprems_of sequent
      (* SOME th on success; NONE only on Auto_Fail (eval_prf_str's whole
         failure vocabulary) — anything else is a bug and must escape. *)
      fun replay (std_time, prf_text) =
        \<^try>\<open>
          SOME (Phi_Sledgehammer_Solver.eval_prf_str kws n
                  (Phi_Proof_Store.tolerant_time std_time) prf_text (ctxt, sequent)
                |> (fn (_, (_, th)) => th))
        catch Phi_Sledgehammer_Solver.Auto_Fail _ => NONE\<close>
      fun try_l1 () =
        case l1_lookup key of
          NONE => NONE
        | SOME (std_time, prf_text) =>
            (case replay (std_time, prf_text) of
               SOME th =>
                 (* L2 is cold on both routes here (miss, or hit-then-tombstone):
                    upgrade-write the row as-is — same key, same time, same
                    text, no format conversion. *)
                 (if write_store
                  then Phi_Proof_Store.update_cached_proof thy (key, (std_time, prf_text))
                  else ()
                  ; SOME (std_time, prf_text, th))
             | NONE => (l1_invalidate key; NONE))
   in case Phi_Proof_Store.get_cached_proof thy key of
        SOME (std_time, prf_text) =>
          (case replay (std_time, prf_text) of
             SOME th => SOME (std_time, prf_text, th)   (*L2 hit: zero write-back*)
           | NONE =>
               (Phi_Proof_Store.invalidate_proof_cache true key thy;
                try_l1 ()))
      | NONE => try_l1 ()
  end

end
