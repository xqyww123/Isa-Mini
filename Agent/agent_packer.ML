signature MINILANG_AGENT = sig
include MINILANG_AGENT

val unpacker : xcmd MessagePackBinIO.Unpack.unpacker

end

structure MiniLang_Agent : MINILANG_AGENT = struct
open MiniLang_Agent

local open MessagePackBinIO.Unpack
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
     | "RULE"     => apfst UNFOLD   o unpackList unpackString
     | "CASE_SPLIT" => apfst CASE_SPLIT o unpackPair (unpackString, unpackOption unpackString)
     | "INDUCT"   => apfst INDUCT   o unpackTuple3 (
                        unpackString,
                        unpackList unpackString,
                        unpackOption unpackString
                     )
     | "ATP"      => apfst ATP      o unpackList unpackString
     | "BRANCH"   => apfst BRANCH   o unpackList unpackString
     | "HAVE"     => apfst HAVE     o unpackList unpackString
     | "OBTAIN"   => apfst OBTAIN   o unpackPair (unpackList unpackString, unpackList unpackString)
     | "ROLLBACK" => apfst ROLLBACK o unpackInt
     | cmd => error("Unknown operation " ^ cmd)
  ) #> apfst snd

end

end
