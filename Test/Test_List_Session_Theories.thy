theory Test_List_Session_Theories
  imports Main
begin

ML \<open>
let
  val target_session = "HOL-Decision_Procs"
  val all_names = Thy_Info.get_names ()
  val matching = all_names
    |> map_filter (fn name =>
        case Thy_Info.lookup_theory name of
          NONE => NONE
        | SOME thy =>
            let val long = Context.theory_long_name thy
                val session = Long_Name.qualifier long
            in if session = target_session then SOME long else NONE end)
    |> sort string_ord
  val _ = tracing (String.concat [
    "Session ", target_session, " has ", Int.toString (length matching), " theories:\n",
    cat_lines matching])
in () end
\<close>

end
