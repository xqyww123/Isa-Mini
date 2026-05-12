theory Test_Infra_Session_Prefixes
  imports "HOL-Decision_Procs.Reflective_Field"
begin

ML \<open>
let
  val thy = @{theory}
  val infra_sessions = ["HOL-Decision_Procs"]
  val prefixes =
    map_filter (fn anc =>
      if member (op =) infra_sessions
           (Long_Name.qualifier (Context.theory_long_name anc))
      then SOME (Context.theory_base_name anc ^ ".")
      else NONE) (Theory.ancestors_of thy)
  val _ = tracing (String.concat [
    "infra_session_thy_prefixes (", Int.toString (length prefixes), "):\n",
    cat_lines (sort string_ord prefixes)])

  val consts = Sign.consts_of thy
  val sample_consts =
    #constants (Consts.dest consts)
    |> map_filter (fn (name, _) =>
         if exists (fn pfx => String.isPrefix pfx name) prefixes
         then SOME name else NONE)
  val _ = tracing (String.concat [
    "\nConstants matching infra prefixes (", Int.toString (length sample_consts), "):\n",
    cat_lines (sort string_ord sample_consts)])

  val facts = Global_Theory.facts_of thy
  val sample_thms =
    Facts.dest_static false [] facts
    |> map_filter (fn (name, _) =>
         if exists (fn pfx => String.isPrefix pfx name) prefixes
         then SOME name else NONE)
  val _ = tracing (String.concat [
    "\nTheorems matching infra prefixes (", Int.toString (length sample_thms), "):\n",
    cat_lines (sort string_ord (take 30 sample_thms)),
    if length sample_thms > 30 then "\n  ... (" ^ Int.toString (length sample_thms - 30) ^ " more)" else ""])
in () end
\<close>

end
