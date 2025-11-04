signature MINILANG_AGENT = sig
include MINILANG_AGENT

val unpacker : xcmd MessagePackBinIO.Unpack.unpacker

val serialize : xcmd list -> string
val deserialize : string -> xcmd list

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

val unpacker =
  unpackPair_dep unpackString (
    fn "RETRIEVE" => apfst RETRIEVE o unpackTuple3 (
                        unpackList unpackString,
                        unpackList unpackString,
                        unpackList unpackString
                     )
     | "SIMPLIFY" => apfst SIMPLIFY o unpackList unpackString
     | "UNFOLD"   => apfst UNFOLD   o unpackList unpackString
     | "WITNESS"  => apfst WITNESS  o unpackList unpackString
     | "RULE"     => apfst RULE     o unpackList unpackString
     | "CASE_SPLIT" => apfst CASE_SPLIT o unpackPair (unpackString, unpackOption unpackString)
     | "INDUCT"   => apfst INDUCT   o unpackTuple3 (
                        unpackString,
                        unpackList unpackString,
                        unpackOption unpackString
                     )
     | "ATP"      => apfst ATP      o unpackList unpackString
     | "NEXT"     => apfst ATP      o unpackList unpackString
     | "END"      => apfst ATP      o unpackList unpackString
     | "BRANCH"   => apfst BRANCH   o unpackList unpackString
     | "HAVE"     => apfst HAVE     o unpackList unpackString
     | "OBTAIN"   => apfst OBTAIN   o unpackPair (
                          unpackList (unpackPair (unpackString, unpackOption unpackString)),
                          unpackList unpackString)
     | "ROLLBACK" => apfst ROLLBACK o unpackInt
     | cmd => error("Unknown operation " ^ cmd)
  ) #> apfst snd

fun packer (RETRIEVE data) =
      packPair (packString,
        packTuple3 (packList packString, packList packString, packList packString))
        ("RETRIEVE", data)
  | packer (SIMPLIFY data) = packPair (packString, packList packString) ("SIMPLIFY", data)
  | packer (UNFOLD data) = packPair (packString, packList packString) ("UNFOLD", data)
  | packer (WITNESS data) =
      packPair (packString, packList packString)
        ("WITNESS", data)
  | packer (RULE data) =
      packPair (packString, packList packString)
        ("RULE", data)
  | packer (CASE_SPLIT data) =
      packPair (packString, packPair (packString, packOption packString))
        ("CASE_SPLIT", data)
  | packer (INDUCT data) =
      packPair (packString, packTuple3 (packString, packList packString, packOption packString))
        ("INDUCT", data)
  | packer (ATP data) =
      packPair (packString, packList packString)
        ("ATP", data)
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
  | packer (ROLLBACK data) = packPair (packString, packInt) ("ROLLBACK", data)

end

end

structure MiniLang_Agent : MINILANG_AGENT = struct
open MiniLang_Agent

structure ML_BinIO = MiniLang_Agent_Pack(BinIO.StreamIO)
structure ML_Bytes = MiniLang_Agent_Pack(BytesIO)

val unpacker = ML_BinIO.unpacker

fun serialize cmds =
  let val buf = BytesIO.mkOutstream ()
   in ML_Bytes.MP.Pack.packList ML_Bytes.packer cmds buf
    ; BytesIO.toString buf
  end

fun deserialize str =
  let val buf = BytesIO.fromString str
   in ML_Bytes.MP.Unpack.unpackList ML_Bytes.unpacker buf
   |> fst
  end

end
