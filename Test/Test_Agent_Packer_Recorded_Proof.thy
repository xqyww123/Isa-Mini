theory Test_Agent_Packer_Recorded_Proof
  imports Minilang_AoA.Minilang_AoA
begin

text \<open>
  The op-stream codec's recorded-proof slot (FactInTime's recorded proof and
  HAMMER's cached proof).  On the wire it is (method text, (cpu_ms, wall_ms)),
  the pair nested in one slot; the unpacker also accepts the legacy
  (method text, ms), lifted to cpu = wall = ms, and the pre-3a fact pair
  without the slot.  Decoded through the in-memory streams of the one codec,
  the way a blob held in memory (the store's aoa_replay entry) is read.
\<close>

ML \<open>
structure P = MessagePackBinIO.Pack
structure U = MessagePackBinIO.Unpack
structure S = Phi_Proof_Store
open MiniLang_Agent
fun assert b msg = if b then () else error ("FAIL: " ^ msg)

fun instream_of_string s = instream_of_bytes (Byte.stringToBytes s)
fun string_of_output write = Byte.bytesToString (bytes_of_output write)

fun decode s = #1 (U.doUnpack (xcmd_unpacker \<^theory>) (instream_of_string s))
fun encode x = string_of_output (xcmd_packer \<^theory> x)

(*the legacy layouts, hand-packed as an old binary wrote them*)
val legacy_recorded = P.packOption (P.packPair (P.packString, P.packInt))
val legacy_fact = P.packTuple3 (P.packString, P.packOption P.packString, legacy_recorded)
val pre_3a_fact = P.packPair (P.packString, P.packOption P.packString)
fun hammer_payload fact_packer facts recorded =
  string_of_output
    (P.packPair (P.packString, P.packTuple3 (P.packList fact_packer, P.packInt, legacy_recorded))
       ("HAMMER", (facts, 30, recorded)))
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

(*4: a blob a store holds (IsaMini/AoA/Tests/Test_Branch.proof-store, written
  by the former BytesIO twin of the codec) decodes through the in-memory
  instream exactly as the store's replay reads it: the bytes are MessagePack's
  alone, not the IO structure's.  Its HAMMER proofs carry the legacy
  single-time slot, so it cannot be re-encoded byte-identically; test 3 is
  the round trip of the current layout.*)
val stored_b64 =
  "kqCZkqZCUkFOQ0iTkqNwb3OleCA+IDCSo25lZ6V4IDwgMJKkemVyb6V4ID0gMJKmSEFNTUVSk5AektlZKEF1dG9fU2xlZGdlaGFtbWVyLnByZV9zaW1wcm9jX29uX2NvbmNsLCAoYXV0b19zcGxpdCBzaW1wOiAgXDxwaGk+c2xlZGdlaGFtbWVyX3NpbXBzKSlbMV0PkqRORVhUkpDAkqZIQU1NRVKTkB6S2TwoQXV0b19TbGVkZ2VoYW1tZXIucHJlX3NpbXByb2Nfb25fY29uY2wsIChpbnNlcnQgLCBzaW1wKSlbMV0IkqRORVhUkpDAkqZIQU1NRVKTkB6S2TwoQXV0b19TbGVkZ2VoYW1tZXIucHJlX3NpbXByb2Nfb25fY29uY2wsIChpbnNlcnQgLCBzaW1wKSlbMV0HkqRORVhUkpDAkqZIQU1NRVKTkB6S2TwoQXV0b19TbGVkZ2VoYW1tZXIucHJlX3NpbXByb2Nfb25fY29uY2wsIChpbnNlcnQgLCBzaW1wKSlbMV0LkqNFTkSQ"
val (script, ops) = MiniLang_Agent_AoA.decode_blob \<^theory> stored_b64
val _ = assert (script = "") "test4 split script"
val _ = assert (length ops = 9) "test4 op count"
val _ = case ops of
          BRANCH [(SOME "pos", "x > 0"), (SOME "neg", "x < 0"), (SOME "zero", "x = 0")]
          :: HAMMER ([], 30, SOME (_, t15)) :: NEXT ([], NONE) :: _ =>
            assert (S.ms_of_times t15 = (15, 15)) "test4 legacy time lifted"
        | _ => error "FAIL: test4 shape"
val _ = case List.last ops of END [] => () | _ => error "FAIL: test4 ends with END"

val _ = writeln "ALL PASS: Test_Agent_Packer_Recorded_Proof"
\<close>

end
