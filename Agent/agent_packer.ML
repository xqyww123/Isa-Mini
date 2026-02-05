signature MINILANG_AGENT = sig
include MINILANG_AGENT

val xcmd_packer : xcmd MessagePackBinIO.Pack.packer
val xcmd_unpacker : xcmd MessagePackBinIO.Unpack.unpacker

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

val unpacker =
  unpackPair_dep unpackString (
    fn (* "RETRIEVE" => apfst RETRIEVE o unpackTuple3 (
                        unpackList unpackString,
                        unpackList unpackString,
                        unpackList unpackString
                     )
     |*) "SIMPLIFY" => apfst SIMPLIFY o unpackList unpackString
     | "UNFOLD"   => apfst UNFOLD   o unpackList unpackString
     | "WITNESS"  => apfst WITNESS  o unpackList unpackString
     | "RULE"     => apfst RULE     o unpackList unpackString
     | "CASE_SPLIT" => apfst CASE_SPLIT o unpackPair (unpackString, unpackOption unpackString)
     | "INDUCT"   => apfst INDUCT   o unpackTuple3 (
                        unpackString,
                        unpackList unpackString,
                        unpackOption unpackString
                     )
     | "ATP"      => apfst (NEXT_OR_END o rpair NONE) o unpackList unpackString
     | "NEXT"     => apfst NEXT o unpackPair (unpackList unpackString, unpack_opt_var_names)
     | "END"      => apfst END o unpackList unpackString
     | "NEXT_or_END" => apfst NEXT_OR_END o unpackPair (unpackList unpackString, unpack_opt_var_names)
     | "SORRY"    => apfst SORRY    o unpack_opt_var_names
     | "BRANCH"   => apfst BRANCH   o unpackList unpackString
     | "HAVE"     => apfst HAVE     o unpackList unpackString
     | "OBTAIN"   => apfst OBTAIN   o unpackPair (
                          unpackList (unpackPair (unpackString, unpackOption unpackString)),
                          unpackList unpackString)
     | "SKIP"     => apfst (K SKIP) o unpackUnit
     | "HAMMER"   => apfst HAMMER o unpackList unpackString
  (* | "ROLLBACK" => apfst ROLLBACK o unpackInt *)
     | cmd => error("Unknown operation " ^ cmd)
  ) #> apfst snd

fun (* packer (RETRIEVE data) =
      packPair (packString,
        packTuple3 (packList packString, packList packString, packList packString))
        ("RETRIEVE", data)
  | *) packer (SIMPLIFY data) = packPair (packString, packList packString) ("SIMPLIFY", data)
  | packer (UNFOLD data) = packPair (packString, packList packString) ("UNFOLD", data)
  | packer (WITNESS data) =
      packPair (packString, packList packString)
        ("WITNESS", data)
  | packer (RULE data) =
      packPair (packString, packList packString) ("RULE", data)
  | packer (CASE_SPLIT data) =
      packPair (packString, packPair (packString, packOption packString))
        ("CASE_SPLIT", data)
  | packer (INDUCT data) =
      packPair (packString, packTuple3 (packString, packList packString, packOption packString))
        ("INDUCT", data)
  | packer (NEXT_OR_END data) =
      packPair (packString, packPair (packList packString, pack_opt_var_names))
        ("NEXT_or_END", data)
  | packer (NEXT data) =
      packPair (packString, packPair (packList packString, pack_opt_var_names))
        ("NEXT", data)
  | packer (END data) = packPair (packString, packList packString) ("END", data)
  | packer (BRANCH data) =
      packPair (packString, packList packString)
        ("BRANCH", data)
  | packer (HAVE data) =
      packPair (packString, packList packString)
        ("HAVE", data)
  | packer (OBTAIN data) =
      packPair (packString, packPair (
          packList (packPair (packString, packOption packString)),
          packList packString))
        ("OBTAIN", data)
  | packer (SORRY vars) =
      packPair (packString, pack_opt_var_names)
        ("SORRY", vars)
  | packer (HAMMER facts) = packPair (packString, packList packString) ("HAMMER", facts)
  | packer SKIP = packPair (packString, packUnit) ("SKIP", ())
(* | packer (ROLLBACK data) = packPair (packString, packInt) ("ROLLBACK", data) *)

end

end

structure MiniLang_Agent : MINILANG_AGENT = struct
open MiniLang_Agent

structure ML_BinIO = MiniLang_Agent_Pack(BinIO.StreamIO)
structure ML_Bytes = MiniLang_Agent_Pack(BytesIO)

val xcmd_packer = ML_BinIO.packer
val xcmd_unpacker = ML_BinIO.unpacker

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
