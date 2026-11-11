theory Sample_Plugin
  imports Minilang_AoA.Minilang_AoA
begin

text \<open>
  The sample plugin of the test suite (docs/USER_OPERATIONS.md): the ML half
  of four user operations, all resident; their Python half is the package
  sample_plugin/ beside this theory, which the registrations name.
\<close>

ML \<open>
structure Sample_Plugin = struct

(*Apply's own message: the method text, reported once the method ran*)
exception APPLIED of string

local
open MessagePackBinIO.Pack MessagePackBinIO.Unpack MiniLang_Agent_Plugin
val packages = {python_packages = [\<^unchecked_name>\<open>IsaMini.AoA.Tests.sample_plugin\<close>]}
(*the single-command bound Minilang's APPLY_CMD applies*)
fun apply_method text s =
  let val ctxt = Minilang.context_of s
      val bound = Time.fromMilliseconds (Config.get ctxt Minilang.mini_single_cmd_timeout)
   in Minilang.APPLY'' (SOME bound) [] (MiniLang_Agent.read_method_text ctxt text) s end
in

val _ = Theory.setup (
  (*the running example: apply a proof method given as text; a SubgoalMaker*)
  register_user_operation packages
    {name = "Apply", default = true,
     unpack_arg = unpackString, pack_arg = packString,
     run = fn _ => fn text => fn s =>
       let val s' = apply_method text s
           val _ = Minilang.get_reporter () (Minilang.Internal (APPLIED text))
        in s' end,
     pack_message = fn APPLIED text => SOME (packString text) | _ => NONE,
     callbacks = K []}
  (*a StdBlock composing HAVE: opens the block the Python base's END closes*)
  #> register_user_operation packages
    {name = "HaveText", default = true,
     unpack_arg = unpackPair (unpackString, unpackString),
     pack_arg = packPair (packString, packString),
     run = fn config => fn (name, statement) =>
       MiniLang_Agent.interpret config (MiniLang_Agent.HAVE (name, [], [], statement, false)),
     pack_message = K NONE, callbacks = K []}
  (*a Leaf whose run leaves two subgoals and reports no Goals of its own: the
    one-subgoal rule refuses it*)
  #> register_user_operation packages
    {name = "TwoGoals", default = true,
     unpack_arg = unpackUnit, pack_arg = packUnit,
     run = fn _ => fn () => fn s => #1 (Minilang.record_reporter (apply_method "(rule conjI)") s),
     pack_message = K NONE, callbacks = K []}
  (*a SubgoalMaker composing a two-case BRANCH: the input gate refuses a schematic goal*)
  #> register_user_operation packages
    {name = "Consider", default = true,
     unpack_arg = unpackPair (unpackString, unpackString),
     pack_arg = packPair (packString, packString),
     run = fn config => fn (first, second) =>
       MiniLang_Agent.interpret config
         (MiniLang_Agent.BRANCH [(SOME "first", first), (SOME "second", second)]),
     pack_message = K NONE, callbacks = K []})

end
end
\<close>

end
