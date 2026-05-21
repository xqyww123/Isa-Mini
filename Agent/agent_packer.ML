signature MINILANG_AGENT = sig
include MINILANG_AGENT

val xcmd_packer : xcmd MessagePackBinIO.Pack.packer
val xcmd_unpacker : xcmd MessagePackBinIO.Unpack.unpacker

val pack_bindings : bindings MessagePackBinIO.Pack.packer
val pack_raw_term : term MessagePackBinIO.Pack.packer
val unpack_raw_term : term MessagePackBinIO.Unpack.unpacker

(*
val serialize : driver * xcmd list -> string
val deserialize : string -> driver * xcmd list
*)

end

functor MiniLang_Agent_Pack(S : sig
                      type instream
                      type outstream
                      val input1 : instream -> (Word8.word * instream) option
                      val inputN : instream * int -> Word8Vector.vector * instream
                      val output : outstream * Word8Vector.vector -> unit
                      val output1 : outstream * Word8.word -> unit
                    end) = struct
structure MP = MessagePack(S)
local open MiniLang_Agent MP.Unpack MP.Pack
in

val unpack_opt_var_names =
  unpackOption (unpackList (unpackOption unpackString))

val pack_opt_var_names =
  packOption (packList (packOption packString))

(* Term and Type serialization - copied from REPL_Serialize for compatibility *)
fun pack_raw_typ (Type data) =
      packPair (packInt, packPair (packString, packList pack_raw_typ)) (0, data)
  | pack_raw_typ (TFree data) =
      packPair (packInt, packPair (packString, packList packString)) (1, data)
  | pack_raw_typ (TVar ((n,i),s)) =
      packPair (packInt, packTuple3 (packString, packInt, packList packString)) (2, (n,i,s))

fun unpack_raw_typ s =
      unpackPair_dep' unpackInt (
        fn 0 => unpackPair (unpackString, unpackList unpack_raw_typ)
             #> apfst Type
         | 1 => unpackPair (unpackString, unpackList unpackString)
             #> apfst TFree
         | 2 => unpackTuple3 (unpackString, unpackInt, unpackList unpackString)
             #> apfst (fn (n,i,s) => TVar ((n,i),s))
         | _ => raise Unpack) s

fun pack_raw_term (Const data) =
      packPair (packInt, packPair (packString, pack_raw_typ)) (3, data)
  | pack_raw_term (Free data) =
      packPair (packInt, packPair (packString, pack_raw_typ)) (4, data)
  | pack_raw_term (Var ((n,i),t)) =
      packPair (packInt, packTuple3 (packString, packInt, pack_raw_typ)) (5, (n,i,t))
  | pack_raw_term (Bound data) =
      packPair (packInt, packInt) (6, data)
  | pack_raw_term (Abs data) =
      packPair (packInt, packTuple3 (packString, pack_raw_typ, pack_raw_term)) (7, data)
  | pack_raw_term (A $ B) =
      packPair (packInt, packPair (pack_raw_term, pack_raw_term)) (8, (A,B))

fun unpack_raw_term s =
      unpackPair_dep' unpackInt (
        fn 3 => unpackPair (unpackString, unpack_raw_typ)
             #> apfst Const
         | 4 => unpackPair (unpackString, unpack_raw_typ)
             #> apfst Free
         | 5 => unpackTuple3 (unpackString, unpackInt, unpack_raw_typ)
             #> apfst (fn (n,i,s) => Var ((n,i),s))
         | 6 => unpackInt #> apfst Bound
         | 7 => unpackTuple3 (unpackString, unpack_raw_typ, unpack_raw_term)
             #> apfst Abs
         | 8 => unpackPair (unpack_raw_term, unpack_raw_term)
             #> apfst (fn (A,B) => A $ B)
         | _ => raise Unpack) s

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

fun pack_extended_fact (FactByName name) =
      packPair (packInt, packString) (0, name)
  | pack_extended_fact (FactInTime stmt) =
      packPair (packInt, packString) (1, stmt)

val unpack_extended_fact =
  unpackPair_dep' unpackInt (fn 0 => unpackString >> FactByName
                              | 1 => unpackString >> FactInTime
                              | n => error ("Unknown extended_fact tag: " ^ Int.toString n))

val unpacker =
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
     | "RULE"     => apfst RULE     o unpackList unpack_extended_fact
     | "CASE_SPLIT" => apfst CASE_SPLIT o unpackTuple4 (
                        unpackString,
                        unpack_opt_var_names,
                        unpackOption unpackString,
                        unpackBool                   (* no_simp *)
                     )
     | "INDUCT"   => apfst INDUCT   o unpackTuple6 (
                        unpackString,                (* target *)
                        unpack_opt_var_names,        (* vars *)
                        unpackList unpackString,     (* arbitrary *)
                        unpackList unpackString,     (* facts_to_generalize *)
                        unpackOption unpackString,   (* rule *)
                        unpackBool                   (* no_simp *)
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
     | "HAMMER"   => apfst HAMMER o unpackPair (unpackList unpack_extended_fact, unpackInt)
     | "INTRO"    => (fn s =>
            let val ((bindings, split_conj), s') =
                    unpackPair (unpackOption unpack_bindings, unpackBool) s
                val _ = if split_conj
                        then error "INTRO no longer supports split_conj; use SPLIT_CONJS"
                        else ()
            in (INTRO bindings, s') end)
     | "SPLIT_CONJS" => apfst (K SPLIT_CONJS) o unpackUnit
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
     | cmd => error("Unknown operation " ^ cmd)
  ) #> apfst snd

fun packer (SIMPLIFY data) =
      packPair (packString, packTuple5 (
                  packList (packPair (pack_extended_fact, packOption (packList pack_raw_term))),
                  packBool,
                  packList packString,
                  packBool,
                  packOption pack_bindings
                )) ("SIMPLIFY", data)
  | packer (UNFOLD data) =
      packPair (packString, packList pack_extended_fact) ("UNFOLD", data)
  | packer (WITNESS data) =
      packPair (packString, packList packString) ("WITNESS", data)
  | packer (RULE data) =
      packPair (packString, packList pack_extended_fact) ("RULE", data)
  | packer (CASE_SPLIT data) =
      packPair (packString, packTuple3 (packString, pack_opt_var_names, packOption packString))
        ("CASE_SPLIT", data)
  | packer (INDUCT data) =
      packPair (packString, packTuple5 (packString, pack_opt_var_names,
                                         packList packString,
                                         packList packString,
                                         packOption packString))
        ("INDUCT", data)
  | packer (NEXT_OR_END data) =
      packPair (packString, packPair (packList pack_extended_fact, pack_opt_var_names))
        ("NEXT_or_END", data)
  | packer (NEXT data) =
      packPair (packString, packPair (packList pack_extended_fact, pack_opt_var_names))
        ("NEXT", data)
  | packer (END data) = packPair (packString, packList pack_extended_fact) ("END", data)
  | packer (BRANCH data) =
      packPair (packString, packList (packPair (packOption packString, packString))) ("BRANCH", data)
  | packer (HAVE (name, fixes, assumes, conclusion, auto_apply)) =
      packPair (packString, packTuple5 (
          packString,
          packList (packPair (packString, packOption packString)),
          packList (packPair (packOption packString, packString)),
          packString,
          packBool)) ("HAVE", (name, fixes, assumes, conclusion, auto_apply))
  | packer (SUFFICES (fixes, assumes, conclusion)) =
      packPair (packString, packTuple3 (
          packList (packPair (packString, packOption packString)),
          packList (packPair (packOption packString, packString)),
          packString)) ("SUFFICES", (fixes, assumes, conclusion))
  | packer (OBTAIN data) =
      packPair (packString, packPair (
          packList (packPair (packString, packOption packString)),
          packList (packPair (packOption packString, packString))))
        ("OBTAIN", data)
  | packer (SORRY_NEXT data) =
      packPair (packString, pack_opt_var_names)
        ("SORRY_NEXT", data)
  | packer (SORRY_END_ALL data) =
      packPair (packString, pack_opt_var_names)
        ("SORRY_END_ALL", data)
  | packer SORRY_ONLY =
      packPair (packString, packUnit) ("SORRY_ONLY", ())
  | packer (HAMMER data) = packPair (packString, packPair (packList pack_extended_fact, packInt)) ("HAMMER", data)
  | packer (INTRO data) = packPair (packString, packOption pack_bindings) ("INTRO", data)
  | packer SPLIT_CONJS = packPair (packString, packUnit) ("SPLIT_CONJS", ())
  | packer (SPECIALIZE data) =
      packPair (packString, packTuple4 (
          packString,
          pack_extended_fact,
          packList (packPair (packString, packString)),
          packList pack_extended_fact))
        ("SPECIALIZE", data)
  | packer (CHAINING data) =
      packPair (packString,
                packPair (packOption packString, packList pack_extended_fact))
        ("CHAINING", data)
  | packer (DEFINE data) =
      packPair (packString,
                packTuple4 (packString,
                            packOption packString,
                            packList packString,
                            packList packString))
        ("DEFINE", data)
  | packer SKIP = packPair (packString, packUnit) ("SKIP", ())
  | packer (CONTRADICTION data) =
      packPair (packString, packString) ("CONTRADICTION", data)
  | packer (SETUP_REWRITING (name, for_any, conditions, redex, residue)) =
      packPair (packString, packTuple5 (
          packString,
          packList (packPair (packString, packOption packString)),
          packList (packPair (packOption packString, packString)),
          packString, packString))
        ("SETUP_REWRITING", (name, for_any, conditions, redex, residue))
(* | packer (ROLLBACK data) = packPair (packString, packInt) ("ROLLBACK", data) *)

end

end

structure MiniLang_Agent : MINILANG_AGENT = struct
open MiniLang_Agent

structure ML_BinIO = MiniLang_Agent_Pack(BinIO.StreamIO)
structure ML_Bytes = MiniLang_Agent_Pack(BytesIO)

val xcmd_packer = ML_BinIO.packer
val xcmd_unpacker = ML_BinIO.unpacker
val pack_bindings = ML_BinIO.pack_bindings
val pack_raw_term = ML_BinIO.pack_raw_term
val unpack_raw_term = ML_BinIO.unpack_raw_term

(*
fun serialize cfg_cmds =
  let val buf = BytesIO.mkOutstream ()
      open ML_Bytes.MP.Pack
   in packPair (packString, packList ML_Bytes.packer) cfg_cmds buf
    ; BytesIO.toString buf
  end

fun deserialize str =
  let val buf = BytesIO.fromString str
      open ML_Bytes.MP.Unpack
   in unpackPair (unpackString, unpackList ML_Bytes.unpacker) buf
   |> fst
  end
*)

end
