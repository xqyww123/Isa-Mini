theory User_Operation_Test_Base
  imports Minilang_AoA.Minilang_AoA
begin

text \<open>
  What the user-operation test theories share: the assertion helpers, the
  argument helper, and an opaque goal with the fact that closes it, which the
  preprocessing segments cannot close on their own (the replay tests).
\<close>

consts Opaque :: bool
lemma opaque: Opaque sorry

ML \<open>
structure User_Operation_Test = struct

fun assert msg b = if b then () else error msg

(*the message of an exception: a remote failure's own text (exn_message would
  escape its quotes), any other's rendering with its markup stripped (under
  PIDE a quoted name may carry markup, invisible in the REPL's output); a
  message that is no YXML at all -- a text whose own symbols break it -- is
  kept as it is, which is what clean_output does*)
fun message_of (Remote_Procedure_Calling.Remote_Calling_Failure {message, ...}) = message
  | message_of exn = Protocol_Message.clean_output (Runtime.exn_message exn)

(*the message of the exception f raises (an interrupt is not one)*)
fun failure_of f =
  (case Exn.result f () of
      Exn.Exn exn => message_of exn
    | Exn.Res _ => error "expected a failure")

(*f must raise an exception whose message contains text*)
fun fails_with text f =
  let val msg = failure_of f
   in assert ("expected the error " ^ quote text ^ ", got " ^ quote msg) (String.isSubstring text msg) end

(*f must raise an exception whose message is exactly text*)
fun fails_exactly text f =
  let val msg = failure_of f
   in assert ("expected exactly the error " ^ quote text ^ ", got " ^ quote msg) (msg = text) end

(*the argument as the codec hands it over: read by the registration's own
  unpack_arg into the type that registration hides, and shown inverse: packed
  by pack_arg back into the bytes unpack_arg read*)
fun argument thy name packed =
  let val operation = #operation (MiniLang_Agent_Plugin.the_operation thy name)
      val bytes = MiniLang_Agent.bytes_of_output packed
      val v = #1 (#unpack_arg operation (MiniLang_Agent.instream_of_bytes bytes))
      val _ = assert (name ^ ": pack_arg inverts unpack_arg")
                (MiniLang_Agent.bytes_of_output (#pack_arg operation v) = bytes)
   in v end

end
\<close>

end
