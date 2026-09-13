theory Test_Proof_Store_Hash_Hit
  imports Minilang_AoA.Minilang_AoA
begin

text \<open>
  The AoA side of the proof store's second key: store_hit_replay's three
  levels and the wiring of hammer_or_AoA.  Numbered as in
  auto_sledgehammer/ai-artifacts/PROOF_STORE_DOUBLE_KEY_PLAN.md section 4.
  Every proof id here carries the prefix TPSHH., which no production writer
  mints (run_AoA writes hex digests, hammer_or_AoA forwards phi obligation
  ids): the level-3 lookups miss by construction, with or without a Python
  behind the L1 RPCs, and the user's L1 cache is never read or invalidated.
  Every block empties the store first, so that it holds under a partial
  re-evaluation as much as under a fresh one.
\<close>

declare [[enable_proof_store = true]]

ML \<open>
structure F = Proof_Store_Format
structure S = Phi_Proof_Store

val thy = \<^theory>
val path = S.store_path thy

fun frames () = if File.is_file path then F.scan (Bytes.content (Bytes.read path)) else []
fun puts_of id =
  map_filter (fn F.PUT (r as {id = id', ...}) => if id' = id then SOME r else NONE | _ => NONE)
             (frames ())
fun tombs_of id = length (filter (fn F.TOMB i => i = id | _ => false) (frames ()))
fun assert b msg = if b then () else error ("FAIL: " ^ msg)

val t1 = S.times_of_ms (100, 100)
fun goal_of ctxt s = Goal.init (Thm.cterm_of ctxt (Syntax.read_prop ctxt s))
fun hit key hash {write} cs =
  Proof_Store_AoA.store_hit_replay {key = key, hash = hash, write_store = write} cs

(*counted by the method below: a replay the skip rule suppresses shows as a
  count that did not move*)
val replays = Unsynchronized.ref 0
\<close>

method_setup count_fail =
  \<open>Scan.succeed (fn _ => SIMPLE_METHOD (fn _ => (replays := !replays + 1; Seq.empty)))\<close>
  "count the invocation, then fail"

ML \<open>
val _ = S.invalidate_store thy
val ctxt = \<^context>
(*20: a hit by hash is promoted under the caller's key when write_store is on*)
val g20 = goal_of ctxt "(x::nat) + 0 = x"
val h20 = Hasher.all_goals (ctxt, g20)
val _ = S.update_cached_proof thy {id = "TPSHH.id1", hash = SOME h20, rewrites = false} (t1, "(simp)[1]")
val r20 = hit "TPSHH.id2" (SOME h20) {write = true} (ctxt, g20)
val _ = assert (Option.map #2 r20 = SOME "(simp)[1]") "test20 hit"
val _ = assert (map #hash (puts_of "TPSHH.id2") = [SOME h20]) "test20 promoted"
val n20 = length (frames ())
val r20' = hit "TPSHH.id3" (SOME h20) {write = false} (ctxt, g20)
val _ = assert (Option.map #2 r20' = SOME "(simp)[1]") "test20 hit again"
val _ = assert (length (frames ()) = n20) "test20 no frame without write_store"

(*20b: a hit by id is handed back as it stands: nothing written.  The preset
      has no hash while the call has one, so a stray promotion write would
      differ from it and could not be short-circuited.*)
val _ = S.update_cached_proof thy {id = "TPSHH.K20b", hash = NONE, rewrites = false} (t1, "(simp)[1]")
val n20b = length (frames ())
val r20b = hit "TPSHH.K20b" (SOME h20) {write = true} (ctxt, g20)
val _ = assert (Option.map #2 r20b = SOME "(simp)[1]") "test20b hit"
val _ = assert (length (frames ()) = n20b) "test20b no frame"
\<close>

ML \<open>
val _ = S.invalidate_store thy
val ctxt = \<^context>
(*21: the cascade through store_hit_replay.  K1 holds G1's proof; G0 arrives
     under K1, fails, is tombstoned; G1 arrives under K2 and gets it back by hash.*)
val g21a = goal_of ctxt "(z::nat) + 0 = z"
val g21b = goal_of ctxt "rev (rev (xs::nat list)) = xs"
val p21 = "(rule rev_rev_ident)[1]"
val h21a = Hasher.all_goals (ctxt, g21a)
val h21b = Hasher.all_goals (ctxt, g21b)
val _ = S.update_cached_proof thy {id = "TPSHH.K1", hash = SOME h21b, rewrites = false} (t1, p21)
val r21a = hit "TPSHH.K1" (SOME h21a) {write = true} (ctxt, g21a)
val _ = assert (is_none r21a) "test21 first call misses"
val _ = assert (tombs_of "TPSHH.K1" = 1) "test21 tombstone"
val r21b = hit "TPSHH.K2" (SOME h21b) {write = true} (ctxt, g21b)
val _ = assert (Option.map #2 r21b = SOME p21) "test21 verbatim"
val _ = assert (map #hash (puts_of "TPSHH.K2") = [SOME h21b] andalso tombs_of "TPSHH.K2" = 0) "test21 promoted"
\<close>

ML \<open>
val _ = S.invalidate_store thy
val ctxt = \<^context>
(*22: the skip rule must not fire on a DIFFERENT record*)
val g22 = goal_of ctxt "(y::nat) * 1 = y"
val h22 = Hasher.all_goals (ctxt, g22)
val _ = S.update_cached_proof thy {id = "TPSHH.K22", hash = NONE, rewrites = false} (t1, "(fail)[1]")
val _ = S.update_cached_proof thy {id = "TPSHH.id_good", hash = SOME h22, rewrites = false} (t1, "(simp)[1]")
(*the promotion rewrites K22 with another text: the collision guard warns, as it should --
  the one collision this file provokes on purpose; every other block has ids of its own*)
val r22 = hit "TPSHH.K22" (SOME h22) {write = true} (ctxt, g22)
val _ = assert (Option.map #2 r22 = SOME "(simp)[1]") "test22 verbatim"
val _ = assert (tombs_of "TPSHH.K22" = 1 andalso map #hash (puts_of "TPSHH.K22") = [NONE, SOME h22]) "test22 frames"
val _ = S.force_reload thy
val _ = assert (S.get_cached_proof thy "TPSHH.K22" = SOME (t1, "(simp)[1]")) "test22 reload: a copy"

(*22b: the skip rule seen from the positive side: the record that failed
      under the id is NOT replayed again under the hash.  The yardstick is one
      replay's count, measured first through the same channel, so the test
      does not depend on how often one replay invokes the method.*)
val kws = Keyword.no_major_keywords (Thy_Header.get_keywords (Proof_Context.theory_of ctxt))
val g22b = goal_of ctxt "(u::nat) * 1 = u"
val h22b = Hasher.all_goals (ctxt, g22b)
val _ = replays := 0
val _ = \<^try>\<open>ignore (Phi_Sledgehammer_Solver.eval_prf_str kws 1 (S.replay_limits t1) "(count_fail)[1]" (ctxt, g22b))
                 catch Phi_Sledgehammer_Solver.Auto_Fail _ => ()\<close>
val per_replay = !replays
val _ = assert (per_replay > 0) "test22b count_fail is reached"
val _ = S.update_cached_proof thy {id = "TPSHH.K22b", hash = SOME h22b, rewrites = false} (t1, "(count_fail)[1]")
val _ = replays := 0
val r22b = hit "TPSHH.K22b" (SOME h22b) {write = true} (ctxt, g22b)
val _ = assert (is_none r22b) "test22b miss"
val _ = assert (!replays = per_replay) ("test22b replayed once, not twice: " ^ string_of_int (!replays))
val _ = assert (tombs_of "TPSHH.K22b" = 1) "test22b tombstone"
\<close>

ML \<open>
val _ = S.invalidate_store thy
val ctxt = \<^context>
(*23: a hash hit that fails to replay writes nothing and forgets the hash only*)
val g23 = goal_of ctxt "rev (rev (ys::nat list)) = ys"
val h23 = Hasher.all_goals (ctxt, g23)
val _ = S.update_cached_proof thy {id = "TPSHH.id23a", hash = SOME h23, rewrites = false} (t1, "(fail)[1]")
val n23 = length (frames ())
val _ = assert (length (puts_of "TPSHH.id23a") = 1) "test23 preset"
val r23 = hit "TPSHH.id23b" (SOME h23) {write = true} (ctxt, g23)
val _ = assert (is_none r23) "test23 miss"
val _ = assert (length (frames ()) = n23) "test23 no frame"
val _ = assert (S.get_cached_proof thy "TPSHH.id23a" = SOME (t1, "(fail)[1]")) "test23 id stays"
val _ = assert (S.get_cached_proof_by_hash thy h23 = NONE) "test23 hash gone"
\<close>

ML \<open>
val _ = S.invalidate_store thy
val ctxt = \<^context>
(*24: hammer_or_AoA hands the hash to the lookup: the preset text comes back
     verbatim instead of a searched one*)
val g24 = goal_of ctxt "(u::nat) + 0 = u"
val h24 = Hasher.all_goals (ctxt, g24)
val _ = S.update_cached_proof thy {id = "TPSHH.id24", hash = SOME h24, rewrites = false} (t1, "(simp)[1]")
val (fut24, st24) =
  MiniLang_Agent_AoA.hammer_or_AoA
    {fact_override = Sledgehammer_Fact.no_fact_override, proof_id = SOME "TPSHH.K24",
     hammer_timeout = NONE, async_mode = Phi_Sledgehammer_Solver.Sync,
     read_store = SOME true, write_store = SOME false} ctxt g24
val _ = assert (Future.join fut24 = "(simp)[1]") "test24 verbatim"
val _ = assert (Thm.no_prems st24) "test24 closed"
\<close>

end
