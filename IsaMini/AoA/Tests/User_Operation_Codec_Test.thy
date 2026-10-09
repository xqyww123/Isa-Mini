theory User_Operation_Codec_Test
  imports User_Operation_Test_Base
begin

text \<open>
  The \<open>USER\<close> branch of the op-stream codec (docs/USER_OPERATIONS.md,
  section 2): a user operation's argument round-trips through the
  registration's \<open>pack_arg\<close> and \<open>unpack_arg\<close>; a payload the registration
  does not read, and a name no imported theory registers, each end the read
  with the error that names the operation.
\<close>

ML \<open>
local
open MiniLang_Agent_Plugin User_Operation_Test
structure P = MessagePackBinIO.Pack
structure U = MessagePackBinIO.Unpack

(*an operation whose argument is a pair: a method text and a flag*)
val operation : (string * bool) user_operation =
  {name = "Apply", default = true,
   unpack_arg = U.unpackPair (U.unpackString, U.unpackBool),
   pack_arg = P.packPair (P.packString, P.packBool),
   run = fn _ => fn _ => I, pack_message = K NONE, callbacks = K []}
val thy = \<^theory> |> register_user_operation {python_packages = []} operation

fun bytes_of write = MiniLang_Agent.bytes_of_output write
fun decode thy bytes = #1 (U.doUnpack (MiniLang_Agent.xcmd_unpacker thy) (MiniLang_Agent.instream_of_bytes bytes))
(*the wire shape Python sends: ("USER", (name, payload))*)
fun wire name payload = bytes_of (P.packPair (P.packString, P.packPair (P.packString, I)) ("USER", (name, payload)))
in

(*1: the round trip, in both directions, beside a built-in command in the same stream*)
val sent = wire "Apply" (P.packPair (P.packString, P.packBool) ("(simp)", true))
val cmd = decode thy sent
val _ = (case cmd of MiniLang_Agent.USER ("Apply", _) => () | _ => error "not a USER command")
val _ = assert "re-encoding gives the bytes Python sent" (bytes_of (MiniLang_Agent.xcmd_packer thy cmd) = sent)
val stream = [cmd, MiniLang_Agent.SKIP, cmd]
val again = #1 (U.doUnpack (U.unpackList (MiniLang_Agent.xcmd_unpacker thy))
                 (MiniLang_Agent.instream_of_bytes (bytes_of (P.packList (MiniLang_Agent.xcmd_packer thy) stream))))
val _ = assert "a stream of three round-trips"
          (length again = 3 andalso
           bytes_of (P.packList (MiniLang_Agent.xcmd_packer thy) again)
             = bytes_of (P.packList (MiniLang_Agent.xcmd_packer thy) stream))

(*2: a payload the registration does not read*)
val _ = fails_with "User operation \"Apply\": its argument does not decode"
          (fn () => decode thy (wire "Apply" (P.packInt 7)))

(*3: a name no imported theory registers*)
val _ = fails_with "User operation \"Aply\": no imported theory registers it"
          (fn () => decode thy (wire "Aply" (P.packPair (P.packString, P.packBool) ("(simp)", true))))
val _ = fails_with "User operation \"Apply\": no imported theory registers it"
          (fn () => decode \<^theory> sent)

val _ = writeln "ALL PASS: User_Operation_Codec_Test"
end
\<close>

end
