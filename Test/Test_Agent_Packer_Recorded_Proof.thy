theory Test_Agent_Packer_Recorded_Proof
  imports Minilang_AoA.Minilang_AoA
begin

text \<open>
  The op-stream codec's recorded-proof slot (FactInTime's recorded proof and
  HAMMER's cached proof).  On the wire it is (method text, (cpu_ms, wall_ms)),
  the pair nested in one slot; the unpacker also accepts the legacy
  (method text, ms), lifted to cpu = wall = ms, and the pre-3a fact pair
  without the slot.  Decoded through the BytesIO twin of the unpacker, the
  one that reads a blob held in memory.
\<close>

ML \<open>
structure P = MessagePackBytesIO.Pack
structure U = MessagePackBytesIO.Unpack
structure S = Phi_Proof_Store
open MiniLang_Agent
fun assert b msg = if b then () else error ("FAIL: " ^ msg)

fun decode s = #1 (U.doUnpack xcmd_unpacker_bytes (BytesIO.fromString s))
fun encode x =
  let val outs = BytesIO.mkOutstream () in xcmd_packer_bytes x outs; BytesIO.toString outs end

(*the legacy layouts, hand-packed as an old binary wrote them*)
val legacy_recorded = P.packOption (P.packPair (P.packString, P.packInt))
val legacy_fact = P.packTuple3 (P.packString, P.packOption P.packString, legacy_recorded)
val pre_3a_fact = P.packPair (P.packString, P.packOption P.packString)
fun hammer_payload fact_packer facts recorded =
  let val outs = BytesIO.mkOutstream ()
   in P.packPair (P.packString, P.packTuple3 (P.packList fact_packer, P.packInt, legacy_recorded))
        ("HAMMER", (facts, 30, recorded)) outs;
      BytesIO.toString outs
  end
\<close>

ML \<open>
(*1: a single-time record in both slots lifts to cpu = wall = ms*)
val _ = case decode (hammer_payload legacy_fact
                       [("f", SOME "P x", SOME ("simp", 7)), ("g", NONE, NONE)] (SOME ("metis", 9))) of
          HAMMER ([FactInTime ("f", "P x", SOME ("simp", t7)), FactByName "g"], 30, SOME ("metis", t9)) =>
            (assert (S.ms_of_times t7 = (7, 7)) "test1 fact lifted";
             assert (S.ms_of_times t9 = (9, 9)) "test1 hammer lifted")
        | _ => error "FAIL: test1 shape"

(*2: the pre-3a fact pair, without the slot, still decodes (the outer alternation)*)
val _ = case decode (hammer_payload pre_3a_fact [("f", SOME "P x"), ("g", NONE)] NONE) of
          HAMMER ([FactInTime ("f", "P x", NONE), FactByName "g"], 30, NONE) => ()
        | _ => error "FAIL: test2 shape"

(*3: the current layout round-trips with both times distinct*)
val x3 = HAMMER ([FactInTime ("f", "P x", SOME ("simp", S.times_of_ms (1, 2)))], 30,
                 SOME ("metis", S.times_of_ms (3, 4)))
val _ = case decode (encode x3) of
          HAMMER ([FactInTime ("f", "P x", SOME ("simp", t12))], 30, SOME ("metis", t34)) =>
            (assert (S.ms_of_times t12 = (1, 2)) "test3 fact";
             assert (S.ms_of_times t34 = (3, 4)) "test3 hammer")
        | _ => error "FAIL: test3 shape"

val _ = writeln "ALL PASS: Test_Agent_Packer_Recorded_Proof"
\<close>

end
