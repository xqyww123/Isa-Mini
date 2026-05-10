theory Test_Interrupt_RPC
  imports Minilang_Agent.Minilang_Agent
begin

ML \<open>
val _ = Remote_Procedure_Calling.load ["IsaMini.AoA.test_interrupt"]

val sleep_cmd : (unit, unit) Remote_Procedure_Calling.command = {
  name = "test_sleep_forever",
  arg_schema = MessagePackBinIO.Pack.packUnit,
  ret_schema = MessagePackBinIO.Unpack.unpackUnit,
  callback = [],
  timeout = NONE
}

fun test_sleep_tactic _ (*ctxt*) _ (*using*) (ctxt, st) = Seq.make (fn () =>
  let val _ = Remote_Procedure_Calling.load ["IsaMini.AoA.test_interrupt"]
      val _ = writeln "=== test_sleep tactic: calling Python sleep, cancel me! ==="
      val _ = Remote_Procedure_Calling.call_command sleep_cmd ()
   in SOME (Seq.Result (ctxt, st), Seq.empty)
  end)
\<close>

method_setup test_sleep = \<open>Scan.succeed test_sleep_tactic\<close>

lemma True
  apply (test_sleep)
  oops

end
