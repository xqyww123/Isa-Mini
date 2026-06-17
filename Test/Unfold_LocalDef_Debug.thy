theory Unfold_LocalDef_Debug
  imports Main Minilang.Minilang
begin

ML \<open>
let
  val ctxt0 = Named_Target.theory_init @{theory}
  val fixes = [(Binding.name "double", SOME "nat => nat", NoSyn)]
              : (binding * string option * mixfix) list
  val specs = [((Binding.empty_atts, "double n = n + n"), [], [])]
              : Specification.multi_specs_cmd
  val s0 : Minilang.state = ((ctxt0, []), Symtab.empty, 0)
  val ((ctxt1, _), _, _) = Minilang.FUN'' fixes specs
                              {metric = [], open_on_fail = false} s0
  val facts = Proof_Context.facts_of ctxt1
  val all_facts = Facts.dest_static false [] facts
  val double_facts = filter (fn (name, _) => String.isSubstring "double" name) all_facts
  val _ = writeln ("=== Facts containing 'double' ===")
  val _ = List.app (fn (name, thms) =>
    writeln ("  " ^ name ^ " (" ^ string_of_int (length thms) ^ " thms): " ^
             String.concatWith "; " (map (Thm.string_of_thm ctxt1) thms)))
    double_facts
  val results = Minilang.potential_defs_of_const ctxt1 "double" []
  val _ = writeln ("=== potential_defs_of_const \"double\" => " ^
                   string_of_int (length results) ^ " results ===")
  val _ = List.app (fn (name, thm) =>
    writeln ("  " ^ name ^ ": " ^ Thm.string_of_thm ctxt1 thm))
    results
in () end
\<close>

end
