theory Dest_Rules_Demo
  imports Main
begin

text \<open>
  Inspect the names returned by @{ML "Induct.dest_rules"} to understand
  whether the registration key (first element) matches the theorem's
  name hint (@{ML "Thm.get_name_hint"}).
\<close>

ML \<open>
let
  val ctxt = @{context}
  val {type_induct, pred_induct, type_cases, pred_cases, ...} = Induct.dest_rules ctxt
  val N = 5

  fun show_rule label (reg_name, thm) =
    let
      val hint = if Thm.has_name_hint thm then Thm.get_name_hint thm else "(no name hint)"
      val consumes = Rule_Cases.get_consumes thm
      val (info, _) = Rule_Cases.get thm
      val case_names = map (fst o fst) info
    in
      writeln (label ^ ":  reg_name=" ^ reg_name
               ^ "  name_hint=" ^ hint
               ^ "  consumes=" ^ string_of_int consumes
               ^ "  cases=[" ^ commas case_names ^ "]")
    end

  fun show_section label rules =
    (writeln ("=== " ^ label ^ " (" ^ string_of_int (length rules) ^ " total, showing first " ^ string_of_int N ^ ") ===");
     List.app (show_rule label) (take N rules))

  val _ = show_section "type_induct" type_induct
  val _ = show_section "pred_induct" pred_induct
  val _ = show_section "type_cases" type_cases
  val _ = show_section "pred_cases" pred_cases
in () end
\<close>

end
