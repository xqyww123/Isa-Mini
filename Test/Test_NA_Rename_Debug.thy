theory Test_NA_Rename_Debug
  imports Main
begin

text \<open>
  Probe: does a body-scope context produced by two successive
  Proof_Context.add_fixes calls on the same name "n" correctly
  revert the second fix's internal Skolem name (e.g. na__) back to the
  external display name "n"?
\<close>

ML \<open>
local
  val T = @{typ nat}
  fun show (label: string, ctxt: Proof.context, internals: string list) =
    let
      val fixes = Variable.dest_fixes ctxt
      val intern_n = Variable.intern_fixed ctxt "n"
      fun show_fix (ext, intl) = "    " ^ ext ^ "  <->  " ^ intl
      val revert_lines =
        map (fn nm => "    revert_fixed \"" ^ nm ^ "\" = \""
                      ^ Variable.revert_fixed ctxt nm ^ "\"") internals
      val print_lines =
        map (fn nm =>
          let val t = Free (nm, T)
           in "    Syntax.string_of_term  Free(\"" ^ nm ^ "\", nat)  =  "
              ^ Syntax.string_of_term ctxt t
          end) internals
      val msg =
        "=== " ^ label ^ " ===\n" ^
        "  dest_fixes:\n" ^ cat_lines (map show_fix fixes) ^ "\n" ^
        "  intern_fixed \"n\" = \"" ^ intern_n ^ "\"\n" ^
        cat_lines revert_lines ^ "\n" ^
        cat_lines print_lines
     in warning msg end
in

val _ =
  let
    val ctxt0 = @{context} |> Variable.set_body true
    val ([n1], ctxt1) =
      Proof_Context.add_fixes [(Binding.name "n", SOME T, NoSyn)] ctxt0
    val ([n2], ctxt2) =
      Proof_Context.add_fixes [(Binding.name "n", SOME T, NoSyn)] ctxt1
  in
    show ("after 1st add_fixes", ctxt1, [n1]);
    show ("after 2nd add_fixes", ctxt2, [n1, n2])
  end
end
\<close>

end
