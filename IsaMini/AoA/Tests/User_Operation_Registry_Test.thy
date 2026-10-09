theory User_Operation_Registry_Test
  imports User_Operation_Test_Base
begin

text \<open>
  The registries of user operations and tasks (docs/USER_OPERATIONS.md,
  sections 1 and 5.1): what \<open>active_operations\<close> selects and in which order
  (name order), the argument's round trip through the hidden type, how a name
  registered twice fails the theory that holds both, how one registration
  reached through two import paths merges, and the two built-in tasks.
\<close>

ML \<open>
local
open MiniLang_Agent_Plugin User_Operation_Test

(*a registration at the plugin's own argument type, int here*)
fun operation name default : int user_operation =
  {name = name, default = default,
   unpack_arg = MessagePackBinIO.Unpack.unpackInt, pack_arg = MessagePackBinIO.Pack.packInt,
   run = fn _ => fn _ => I, pack_message = K NONE, callbacks = K []}
fun register name default =
  register_user_operation {python_packages = [name ^ "_pkg"]} (operation name default)
fun task name = register_task {python_packages = [name ^ "_pkg"]} {name = name}
val names = map (#name o #operation)
fun begin name parents = Theory.begin_theory (name, Position.none) parents

(*registered out of name order; "Beta" is shorter, so the table's own order
  (fast_string_ord) would put it first*)
val thy = \<^theory> |> register "Gamma" true |> register "Alpha" true |> register "Beta" false
in

(*selection, in name order*)
val _ = assert "the defaults" (names (active_operations thy []) = ["Alpha", "Gamma"])
val _ = assert "an inclusion" (names (active_operations thy [("Beta", true)]) = ["Alpha", "Beta", "Gamma"])
val _ = assert "an exclusion" (names (active_operations thy [("Alpha", false)]) = ["Gamma"])
val _ = assert "both" (names (active_operations thy [("Beta", true), ("Gamma", false)]) = ["Alpha", "Beta"])
val _ = fails_exactly "User operation \"Delta\": no imported theory registers it"
          (fn () => active_operations thy [("Delta", true)])
val _ = assert "the_operation finds the packages" (#python_packages (the_operation thy "Beta") = ["Beta_pkg"])
val _ = fails_exactly "User operation \"Delta\": no imported theory registers it"
          (fn () => the_operation thy "Delta")

(*the argument round trip: packInt's bytes, read by the stored unpack_arg into
  the hidden type, written back by the stored pack_arg*)
val alpha = #operation (the_operation thy "Alpha")
val bytes = MiniLang_Agent.bytes_of_output (MessagePackBinIO.Pack.packInt 42)
val (hidden, _) = #unpack_arg alpha (MiniLang_Agent.instream_of_bytes bytes)
val _ = assert "the argument round-trips through the hidden type"
          (MiniLang_Agent.bytes_of_output (#pack_arg alpha hidden) = bytes)

(*one name registered twice: in one theory, or in two theories one imports*)
val _ = fails_exactly "User operation \"Alpha\" is registered twice" (fn () => thy |> register "Alpha" false)
val thy_a = begin "UOR_A" [\<^theory>] |> register "Dup" true
val thy_b = begin "UOR_B" [\<^theory>] |> register "Dup" true
val _ = fails_exactly "User operation \"Dup\" is registered twice" (fn () => begin "UOR_AB" [thy_a, thy_b])

(*a diamond: the registration of the shared ancestor reaches the join through
  both sides, each of which registered more, so the two tables really merge*)
val thy_a1 = begin "UOR_A1" [thy_a] |> register "Omega" true
val thy_a2 = begin "UOR_A2" [thy_a] |> register "Pi" true
val _ = assert "one registration through two paths, the rest merged, in name order"
          (names (active_operations (begin "UOR_AA" [thy_a1, thy_a2]) []) = ["Dup", "Omega", "Pi"])

(*tasks*)
val _ = assert "usual is registered" (the_task thy "usual" = {python_packages = []})
val _ = assert "learning is registered" (the_task thy "learning" = {python_packages = []})
val _ = fails_exactly "User task \"termination\": no imported theory registers it"
          (fn () => the_task thy "termination")
val thy_t = thy |> task "termination"
val _ = assert "a user task" (the_task thy_t "termination" = {python_packages = ["termination_pkg"]})
val _ = fails_exactly "User task \"usual\" is registered twice"
          (fn () => thy |> register_task {python_packages = []} {name = "usual"})
(*the task registries of two siblings merge: the built-in tasks are in both*)
val thy_t1 = begin "UOR_T1" [\<^theory>] |> task "termination"
val thy_t2 = begin "UOR_T2" [\<^theory>] |> task "invariant"
val thy_tt = begin "UOR_TT" [thy_t1, thy_t2]
val _ = assert "two sibling tasks merge"
          (the_task thy_tt "termination" = {python_packages = ["termination_pkg"]} andalso
           the_task thy_tt "invariant" = {python_packages = ["invariant_pkg"]})
val thy_t2' = begin "UOR_T2'" [\<^theory>] |> task "termination"
val _ = fails_exactly "User task \"termination\" is registered twice" (fn () => begin "UOR_TT'" [thy_t1, thy_t2'])

val _ = writeln "ALL PASS: User_Operation_Registry_Test"
end
\<close>

end
