theory Test_Parse_Debug
  imports Minilang.Minilang
begin

notepad
begin
  fix k :: int

  ML_val \<open>
    val ctxt = \<^context>

    (* What does the old Rule_Insts.where_rule produce? *)
    val thm_orig = @{thm int_le_induct}
    val thm_where = Rule_Insts.where_rule ctxt
        [((("k", 0), Position.none), "k")] [] thm_orig
    val _ = writeln ("where_rule result: " ^ Thm.string_of_thm ctxt thm_where)
    val _ = writeln ("where_rule raw: " ^ ML_Syntax.print_term (Thm.prop_of thm_where))

    val _ = writeln ("is_body: " ^ Bool.toString (Variable.is_body ctxt))
    val fixes = Variable.dest_fixes ctxt
    val _ = writeln ("fixes: " ^ commas (map (fn (ext,int) => ext ^ " -> " ^ int) fixes))

    (* What does Syntax.read_term produce? *)
    val t1 = Syntax.read_term ctxt "k"
    val _ = writeln ("read_term k: " ^ ML_Syntax.print_term t1)

    (* What about read_terms? *)
    val [t2] = Syntax.read_terms ctxt ["k"]
    val _ = writeln ("read_terms k: " ^ ML_Syntax.print_term t2)

    (* What about mode_pattern? *)
    val [t3] = Syntax.read_terms (Proof_Context.set_mode Proof_Context.mode_pattern ctxt) ["k"]
    val _ = writeln ("read_terms pattern k: " ^ ML_Syntax.print_term t3)

    (* What about parse_term + check_term (Rule_Insts approach)? *)
    val t4_parsed = Syntax.parse_term ctxt "k"
    val _ = writeln ("parse_term k: " ^ ML_Syntax.print_term t4_parsed)
    val t4_checked = Syntax.check_term ctxt t4_parsed
    val _ = writeln ("check_term k: " ^ ML_Syntax.print_term t4_checked)
  \<close>

end
end
