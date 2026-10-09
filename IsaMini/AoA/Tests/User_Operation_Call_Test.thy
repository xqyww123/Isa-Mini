theory User_Operation_Call_Test
  imports Sample_Plugin User_Operation_Test_Base
begin

text \<open>
  The start of a call (docs/USER_OPERATIONS.md, sections 5.2 and 8), each case
  ending the call before the agent runs: a selection naming an operation no
  imported theory registers; a task no imported theory registers; a Python
  package that does not import; a callback whose name AoA, a global callback
  or another user operation already holds; a task registered in ML with no
  Python class.  The calls run under the RPC host with the test driver.
\<close>

ML \<open>
local
open MiniLang_Agent_Plugin User_Operation_Test
open MessagePackBinIO.Pack MessagePackBinIO.Unpack

fun callback name : Remote_Procedure_Calling.callback' =
  Remote_Procedure_Calling.mk_callback
    {name = name, on_interrupt = Remote_Procedure_Calling.Reraise,
     arg_schema = unpackUnit, ret_schema = packUnit, function = K (), timeout = NONE}
fun operation name callbacks : unit user_operation =
  {name = name, default = false, unpack_arg = unpackUnit, pack_arg = packUnit,
   run = fn _ => fn () => I, pack_message = K NONE, callbacks = K callbacks}
fun register name packages callbacks =
  register_user_operation {python_packages = packages} (operation name callbacks)

(*the registrations the cases select; none is a default*)
val thy = \<^theory>
  |> register "CbGlobal" [] [callback "log"]
  |> register "CbFramework" [] [callback "IsaMini.proof_opr"]
  |> register "CbShared1" [] [callback "shared_cb"]
  |> register "CbShared2" [] [callback "shared_cb"]
  |> register "BadPackage" ["no.such.package"] []
  |> register_task {python_packages = []} {name = "ghost"}
val ctxt = Named_Target.theory_init thy
val goal = Goal.init (Thm.cterm_of ctxt \<^prop>\<open>True\<close>)
val (minilang_cfg, budget) = MiniLang_Agent.default_cfg
fun call selection task =
  MiniLang_Agent_AoA.raw_AoA
    {driver = "test", minilang_cfg = minilang_cfg, budget = budget,
     invocation_id = "User_Operation_Call_Test", task = task, user_operations = selection}
    (ctxt, goal)
val usual = MiniLang_Agent_AoA.usual
in
val _ = fails_with "User operation \"Nope\": no imported theory registers it"
          (fn () => call [("Nope", true)] usual)
val _ = fails_with "User task \"nope\": no imported theory registers it"
          (fn () => call [] {name = "nope", payload = packString ""})
val _ = fails_with "Fail to load no.such.package"
          (fn () => call [("BadPackage", true)] usual)
val _ = fails_with "Callback \"log\" of a user operation: the name is already taken"
          (fn () => call [("CbGlobal", true)] usual)
val _ = fails_with "Callback \"IsaMini.proof_opr\" of a user operation: the name is already taken"
          (fn () => call [("CbFramework", true)] usual)
val _ = fails_with "Callback \"shared_cb\" of a user operation: the name is already taken"
          (fn () => call [("CbShared1", true), ("CbShared2", true)] usual)
(*registered in ML, no Python class: refused on the Python side, end to end*)
val _ = fails_with "User task \"ghost\": no imported Python package registers a task class under this name."
          (fn () => call [] {name = "ghost", payload = packString ""})
val _ = writeln "ALL PASS: User_Operation_Call_Test"
end
\<close>

end
