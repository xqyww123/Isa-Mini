signature MINILANG_AGENT = sig
include MINILANG_AGENT

(*The one codec of the op stream: the live wire, the proof store's blob and
  its replay.  It takes the theory for the USER branch, which reads and writes
  a user operation's argument with the registration under that name
  (docs/USER_OPERATIONS.md, section 2).*)
val xcmd_packer : theory -> xcmd MessagePackBinIO.Pack.packer
val xcmd_unpacker : theory -> xcmd MessagePackBinIO.Unpack.unpacker

val pack_bindings : bindings MessagePackBinIO.Pack.packer
(*A Phi_Proof_Store.times on the wire: the (cpu_ms, wall_ms) pair in one slot.*)
val pack_times : Phi_Proof_Store.times MessagePackBinIO.Pack.packer
val pack_raw_term : term MessagePackBinIO.Pack.packer
val unpack_raw_term : term MessagePackBinIO.Unpack.unpacker

(*In-memory BinIO streams, so that the one codec above serves the wire, the
  proof store's aoa_replay blob and its replay alike.*)
val instream_of_bytes : Word8Vector.vector -> BinIO.StreamIO.instream
val bytes_of_output : (BinIO.StreamIO.outstream -> unit) -> Word8Vector.vector

end

structure MiniLang_Agent : MINILANG_AGENT = struct
open MiniLang_Agent

structure Codec = RPC_Term_Codec(MessagePackBinIO)
local open MessagePackBinIO.Unpack MessagePackBinIO.Pack
in

val unpack_opt_var_names =
  unpackOption (unpackList (unpackOption unpackString))

val pack_opt_var_names =
  packOption (packList (packOption packString))

(*The raw term codec, Isabelle_RPC's functor over MessagePackBinIO.*)
open Codec

(* Bindings serialization using term packer *)
(* Serialize var_name record {internal_name: string, external_name: string, typ_pretty: string} *)
fun unpack_var_name s =
  let val ((internal_name, external_name, typ_pretty), s') = unpackTuple3 (unpackString, unpackString, unpackString) s
  in ({internal_name = internal_name, external_name = external_name, typ_pretty = typ_pretty}, s')
  end

fun pack_var_name {internal_name, external_name, typ_pretty} =
  packTuple3 (packString, packString, packString) (internal_name, external_name, typ_pretty)

(* Serialize prem_name record {internal_term: term, external_name: string, pretty: string} *)
fun unpack_prem_name s =
  let val ((internal_term, external_name, pretty), s') =
        unpackTuple3 (unpack_raw_term, unpackString, unpackString) s
  in ({internal_term = internal_term, external_name = external_name, pretty = pretty}, s')
  end

fun pack_prem_name {internal_term, external_name, pretty} =
  packTuple3 (pack_raw_term, packString, packString) (internal_term, external_name, pretty)

val unpack_bindings =
  unpackPair (unpackList unpack_var_name, unpackList unpack_prem_name)

val pack_bindings =
  packPair (packList pack_var_name, packList pack_prem_name)

(* A Phi_Proof_Store.times on the wire: the (cpu_ms, wall_ms) pair nested in
   one slot, as at every wire carrying one.  The unpack side ALSO accepts a
   single ms, lifting it to cpu = wall = ms; mlmsgpack's `||` retries on the
   untouched instream, so the fallback is safe.  Shared by the recorded proofs
   below, TACTIC's recorded times and the SH_PRF / FACT_PRF / TACTIC_TIMES
   messages (agent_server.ML). *)
val pack_times = packPair (packInt, packInt) o Phi_Proof_Store.ms_of_times

val unpack_times =
  (unpackPair (unpackInt, unpackInt) || (unpackInt >> (fn ms => (ms, ms))))
  >> Phi_Proof_Store.times_of_ms

(* A recorded proof on the wire: (method text, times).  Shared by FactInTime's
   recorded proof and HAMMER's cached proof. *)
fun pack_recorded_proof (prf, times) = packPair (packString, pack_times) (prf, times)

val unpack_recorded_proof = unpackPair (unpackString, unpack_times)

(* Wire triple (name, stmt option, recorded proof option) — stage 3a, D37.
   The pack side always writes the triple; the unpack side ALSO accepts the
   pre-3a pair, lifting it with a NONE third field: the arity is part of the
   wire format (packOption cannot express a missing field), and `||` retries
   as above. *)
fun pack_extended_fact (FactByName name) =
      packTuple3 (packString, packOption packString, packOption pack_recorded_proof)
                 (name, NONE, NONE)
  | pack_extended_fact (FactInTime (assigned_name, stmt, recorded)) =
      packTuple3 (packString, packOption packString, packOption pack_recorded_proof)
                 (assigned_name, SOME stmt, recorded)

val unpack_extended_fact =
  (unpackTuple3 (unpackString, unpackOption unpackString, unpackOption unpack_recorded_proof)
   || (unpackPair (unpackString, unpackOption unpackString)
       >> (fn (name, stmt) => (name, stmt, NONE))))
  >> (fn (name, NONE, _) => FactByName name
       | (name, SOME stmt, recorded) => FactInTime (name, stmt, recorded))

(* post-rule schematic instantiation: rounds of (var-name, value-string) pairs *)
val unpack_post_insts = unpackList (unpackList (unpackPair (unpackString, unpackString)))
val pack_post_insts   = packList   (packList   (packPair   (packString,   packString)))

fun xcmd_unpacker thy =
  unpackPair_dep unpackString (
    fn "SIMPLIFY" => apfst SIMPLIFY o unpackTuple5 (
                        unpackList (unpackPair (unpack_extended_fact, unpackOption (unpackList unpack_raw_term))),
                        unpackBool,
                        unpackList unpackString,
                        unpackBool,
                        unpackOption unpack_bindings
                     )
     | "UNFOLD"   => apfst UNFOLD   o unpackList unpack_extended_fact
     | "WITNESS"  => apfst WITNESS  o unpackList unpackString
     | "RULE"     => apfst RULE     o unpackPair (
                        unpackList unpack_extended_fact,
                        unpack_post_insts            (* post-rule instantiation rounds *)
                     )
     | "CASE_SPLIT" => apfst CASE_SPLIT o unpackTuple5 (
                        unpackString,
                        unpack_opt_var_names,
                        unpackOption unpackString,
                        unpackBool,                  (* no_simp *)
                        unpack_post_insts            (* post-rule instantiation rounds *)
                     )
     | "INDUCT"   => apfst INDUCT   o unpackTuple7 (
                        unpackString,                (* target *)
                        unpack_opt_var_names,        (* vars *)
                        unpackList unpackString,     (* arbitrary *)
                        unpackList unpackString,     (* facts_to_generalize *)
                        unpackOption unpackString,   (* rule *)
                        unpackBool,                  (* no_simp *)
                        unpack_post_insts            (* post-rule instantiation rounds *)
                     )
     | "ATP"      => apfst (fn (facts, vars) => NEXT_OR_END (facts, vars))
                      o unpackPair (unpackList unpack_extended_fact, unpack_opt_var_names)
     | "NEXT"     => apfst NEXT o unpackPair (unpackList unpack_extended_fact, unpack_opt_var_names)
     | "END"      => apfst END o unpackList unpack_extended_fact
     | "NEXT_or_END" => apfst NEXT_OR_END o unpackPair (unpackList unpack_extended_fact, unpack_opt_var_names)
     | "SORRY_NEXT"    => apfst SORRY_NEXT    o unpack_opt_var_names
     | "SORRY_END_ALL" => apfst SORRY_END_ALL o unpack_opt_var_names
     | "SORRY_ONLY"   => apfst (K SORRY_ONLY) o unpackUnit
     | "BRANCH"   => apfst BRANCH   o unpackList (unpackPair (unpackOption unpackString, unpackString))
     | "HAVE"     => apfst HAVE     o unpackTuple5 (
                        unpackString,
                        unpackList (unpackPair (unpackString, unpackOption unpackString)),
                        unpackList (unpackPair (unpackOption unpackString, unpackString)),
                        unpackString,
                        unpackBool)
     | "SUFFICES" => apfst SUFFICES o unpackTuple3 (
                        unpackList (unpackPair (unpackString, unpackOption unpackString)),
                        unpackList (unpackPair (unpackOption unpackString, unpackString)),
                        unpackString)
     | "OBTAIN"   => apfst OBTAIN   o unpackPair (
                          unpackList (unpackPair (unpackString, unpackOption unpackString)),
                          unpackList (unpackPair (unpackOption unpackString, unpackString)))
     | "HAMMER"   => apfst HAMMER o unpackTuple3 (unpackList unpack_extended_fact, unpackInt,
                        unpackOption unpack_recorded_proof)
     | "INTRO"    => (fn s =>
            let val ((bindings, allow_standard_fallback), s') =
                    unpackPair (unpackOption unpack_bindings, unpackBool) s
            in (INTRO (bindings, allow_standard_fallback), s') end)
     | "SPLIT_CONJS" => apfst (K SPLIT_CONJS) o unpackUnit
     | "SPLIT_CONJS2" => apfst (K SPLIT_CONJS2) o unpackUnit
     | "SPECIALIZE" => apfst SPECIALIZE o unpackTuple4 (
                        unpackString,
                        unpack_extended_fact,
                        unpackList (unpackPair (unpackString, unpackString)),
                        unpackList unpack_extended_fact)
     | "CHAINING" => apfst CHAINING o unpackPair (
                        unpackOption unpackString,
                        unpackList unpack_extended_fact)
     | "DEFINE"   => apfst DEFINE o unpackTuple4 (
                        unpackString,
                        unpackOption unpackString,
                        unpackList unpackString,
                        unpackList unpackString
                     )
     | "SKIP"     => apfst (K SKIP) o unpackUnit
     | "CONTRADICTION" => apfst CONTRADICTION o unpackString
     | "SETUP_REWRITING" => apfst SETUP_REWRITING o unpackTuple5 (
                        unpackString,
                        unpackList (unpackPair (unpackString, unpackOption unpackString)),
                        unpackList (unpackPair (unpackOption unpackString, unpackString)),
                        unpackString, unpackString)
     | "COMPUTE" => apfst COMPUTE o unpackPair (unpackString, unpackString)
     | "INTERPRET" => apfst INTERPRET o
         unpackTuple3 (unpackString, unpackString,
                       unpackList (unpackPair (unpackString, unpackString)))
     | "INST_GOAL_VARS" => apfst INST_GOAL_VARS o
         unpackList (unpackPair (unpackString, unpackString))
     | "USER" => apfst USER o unpackPair_dep unpackString (fn name =>
         let val unpack_arg = #unpack_arg (#operation (MiniLang_Agent_Plugin.the_operation thy name))
          in fn s => unpack_arg s
               handle Unpack => error ("User operation " ^ quote name ^ ": its argument does not decode")
         end)
     | "TACTIC" => apfst TACTIC o unpackTuple5 (
                        unpackString,                (* full method name *)
                        unpackString,                (* arguments *)
                        unpackList unpack_extended_fact,
                        unpack_post_insts,           (* post-rule instantiation rounds *)
                        unpackOption unpack_times    (* recorded times *)
                     )
     | cmd => error("Unknown operation " ^ cmd)
  ) #> apfst snd

fun xcmd_packer _ (SIMPLIFY data) =
      packPair (packString, packTuple5 (
                  packList (packPair (pack_extended_fact, packOption (packList pack_raw_term))),
                  packBool,
                  packList packString,
                  packBool,
                  packOption pack_bindings
                )) ("SIMPLIFY", data)
  | xcmd_packer _ (UNFOLD data) =
      packPair (packString, packList pack_extended_fact) ("UNFOLD", data)
  | xcmd_packer _ (WITNESS data) =
      packPair (packString, packList packString) ("WITNESS", data)
  | xcmd_packer _ (RULE data) =
      packPair (packString, packPair (packList pack_extended_fact, pack_post_insts))
        ("RULE", data)
  | xcmd_packer _ (CASE_SPLIT data) =
      packPair (packString, packTuple5 (packString, pack_opt_var_names, packOption packString,
                                         packBool, pack_post_insts))
        ("CASE_SPLIT", data)
  | xcmd_packer _ (INDUCT data) =
      packPair (packString, packTuple7 (packString, pack_opt_var_names,
                                         packList packString,
                                         packList packString,
                                         packOption packString,
                                         packBool,
                                         pack_post_insts))
        ("INDUCT", data)
  | xcmd_packer _ (NEXT_OR_END data) =
      packPair (packString, packPair (packList pack_extended_fact, pack_opt_var_names))
        ("NEXT_or_END", data)
  | xcmd_packer _ (NEXT data) =
      packPair (packString, packPair (packList pack_extended_fact, pack_opt_var_names))
        ("NEXT", data)
  | xcmd_packer _ (END data) = packPair (packString, packList pack_extended_fact) ("END", data)
  | xcmd_packer _ (BRANCH data) =
      packPair (packString, packList (packPair (packOption packString, packString))) ("BRANCH", data)
  | xcmd_packer _ (HAVE (name, fixes, assumes, conclusion, auto_apply)) =
      packPair (packString, packTuple5 (
          packString,
          packList (packPair (packString, packOption packString)),
          packList (packPair (packOption packString, packString)),
          packString,
          packBool)) ("HAVE", (name, fixes, assumes, conclusion, auto_apply))
  | xcmd_packer _ (SUFFICES (fixes, assumes, conclusion)) =
      packPair (packString, packTuple3 (
          packList (packPair (packString, packOption packString)),
          packList (packPair (packOption packString, packString)),
          packString)) ("SUFFICES", (fixes, assumes, conclusion))
  | xcmd_packer _ (OBTAIN data) =
      packPair (packString, packPair (
          packList (packPair (packString, packOption packString)),
          packList (packPair (packOption packString, packString))))
        ("OBTAIN", data)
  | xcmd_packer _ (SORRY_NEXT data) =
      packPair (packString, pack_opt_var_names)
        ("SORRY_NEXT", data)
  | xcmd_packer _ (SORRY_END_ALL data) =
      packPair (packString, pack_opt_var_names)
        ("SORRY_END_ALL", data)
  | xcmd_packer _ SORRY_ONLY =
      packPair (packString, packUnit) ("SORRY_ONLY", ())
  | xcmd_packer _ (HAMMER (facts, timeout, cached)) =
      packPair (packString, packTuple3 (packList pack_extended_fact, packInt,
                packOption pack_recorded_proof))
        ("HAMMER", (facts, timeout, cached))
  | xcmd_packer _ (INTRO (bindings, allow_standard_fallback)) =
      packPair (packString, packPair (packOption pack_bindings, packBool))
               ("INTRO", (bindings, allow_standard_fallback))
  | xcmd_packer _ SPLIT_CONJS = packPair (packString, packUnit) ("SPLIT_CONJS", ())
  | xcmd_packer _ SPLIT_CONJS2 = packPair (packString, packUnit) ("SPLIT_CONJS2", ())
  | xcmd_packer _ (SPECIALIZE data) =
      packPair (packString, packTuple4 (
          packString,
          pack_extended_fact,
          packList (packPair (packString, packString)),
          packList pack_extended_fact))
        ("SPECIALIZE", data)
  | xcmd_packer _ (CHAINING data) =
      packPair (packString,
                packPair (packOption packString, packList pack_extended_fact))
        ("CHAINING", data)
  | xcmd_packer _ (DEFINE data) =
      packPair (packString,
                packTuple4 (packString,
                            packOption packString,
                            packList packString,
                            packList packString))
        ("DEFINE", data)
  | xcmd_packer _ SKIP = packPair (packString, packUnit) ("SKIP", ())
  | xcmd_packer _ (CONTRADICTION data) =
      packPair (packString, packString) ("CONTRADICTION", data)
  | xcmd_packer _ (SETUP_REWRITING (name, for_any, conditions, redex, residue)) =
      packPair (packString, packTuple5 (
          packString,
          packList (packPair (packString, packOption packString)),
          packList (packPair (packOption packString, packString)),
          packString, packString))
        ("SETUP_REWRITING", (name, for_any, conditions, redex, residue))
  | xcmd_packer _ (COMPUTE (name, term)) =
      packPair (packString, packPair (packString, packString)) ("COMPUTE", (name, term))
  | xcmd_packer _ (INTERPRET (qualifier, locale, insts)) =
      packPair (packString, packTuple3 (
          packString, packString, packList (packPair (packString, packString))))
        ("INTERPRET", (qualifier, locale, insts))
  | xcmd_packer _ (INST_GOAL_VARS pairs) =
      packPair (packString, packList (packPair (packString, packString)))
        ("INST_GOAL_VARS", pairs)
  | xcmd_packer thy (USER (name, arg)) =
      packPair (packString,
                packPair (packString, #pack_arg (#operation (MiniLang_Agent_Plugin.the_operation thy name))))
        ("USER", (name, arg))
  | xcmd_packer _ (TACTIC data) =
      packPair (packString, packTuple5 (packString, packString, packList pack_extended_fact,
                                         pack_post_insts, packOption pack_times))
        ("TACTIC", data)

end

fun instream_of_bytes v =
  BinIO.StreamIO.mkInstream (BinPrimIO.openVector v, Word8Vector.fromList [])

fun bytes_of_output write =
  let val chunks = Unsynchronized.ref ([] : Word8Vector.vector list)
      fun write_vec slice =
        (chunks := Word8VectorSlice.vector slice :: ! chunks; Word8VectorSlice.length slice)
      val writer = BinPrimIO.augmentWriter (BinPrimIO.WR {
            name = "bytes_of_output", chunkSize = 4096,
            writeVec = SOME write_vec, writeArr = NONE, writeVecNB = NONE, writeArrNB = NONE,
            block = NONE, canOutput = NONE, getPos = NONE, setPos = NONE, endPos = NONE,
            verifyPos = NONE, close = I, ioDesc = NONE})
      val outs = BinIO.StreamIO.mkOutstream (writer, IO.BLOCK_BUF)
      (*closeOut flushes and drops the stream from Poly/ML's global stream list*)
      val () = \<^try>\<open>write outs finally BinIO.StreamIO.closeOut outs\<close>
   in Word8Vector.concat (rev (! chunks)) end

end
