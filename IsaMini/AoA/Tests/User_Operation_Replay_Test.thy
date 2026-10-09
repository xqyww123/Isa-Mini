theory User_Operation_Replay_Test
  imports Sample_Plugin User_Operation_Test_Base
begin

text \<open>
  A stored proof made of user operations replays (docs/USER_OPERATIONS.md,
  section 2): the blob, assembled by the one encoder raw_AoA uses, is decoded
  and run by aoa_replay in a context whose theory imports the plugin -- a
  SubgoalMaker's step, and a StdBlock's block opened by the operation and
  closed by END; in a context whose theory does not import the plugin, and
  differs in nothing else, the same blob is a stale entry and the replay
  fails.  The goal is the test base's opaque constant.
\<close>

ML \<open>
local
open MiniLang_Agent User_Operation_Test

val thy = \<^theory>
val ctxt = Named_Target.theory_init thy
(*a context whose theory does not import the plugin*)
val ctxt0 = Named_Target.theory_init \<^theory>\<open>User_Operation_Test_Base\<close>
(*the one goal, certified in the test base itself, an ancestor of both contexts*)
val goal = Goal.init (Thm.global_cterm_of \<^theory>\<open>User_Operation_Test_Base\<close> \<^prop>\<open>Opaque\<close>)

fun apply text = USER ("Apply", argument thy "Apply" (MessagePackBinIO.Pack.packString text))
fun have_text (name, statement) =
  USER ("HaveText", argument thy "HaveText"
          (MessagePackBinIO.Pack.packPair (MessagePackBinIO.Pack.packString, MessagePackBinIO.Pack.packString)
             (name, statement)))

(*the blob as raw_AoA assembles it; every stream ends with the END that closes
  the top-level block*)
fun blob xcmds = MiniLang_Agent_AoA.encode_blob thy ("", xcmds @ [END []])
fun replay ctxt b64 = Seq.pull (MiniLang_Agent_AoA.aoa_replay_method b64 [] (ctxt, goal))
fun closes msg ctxt b64 =
  (case replay ctxt b64 of
     SOME (Seq.Result (_, th), _) => assert (msg ^ ": the replayed proof closes the goal") (Thm.no_prems th)
   | _ => error (msg ^ ": the replay failed"))
in

(*1: a SubgoalMaker's step*)
val _ = closes "Apply" ctxt (blob [apply "(rule opaque)"])

(*2: the same blob, the same goal, in the context whose theory does not import
  the plugin: stale*)
val _ = assert "a stale entry does not replay" (is_none (replay ctxt0 (blob [apply "(rule opaque)"])))

(*3: a StdBlock's block, opened by the operation, closed by END, its fact used after*)
val _ = closes "HaveText" ctxt
          (blob [have_text ("h", "Opaque"), apply "(rule opaque)", END [], apply "(rule h)"])

val _ = writeln "ALL PASS: User_Operation_Replay_Test"
end
\<close>

end
