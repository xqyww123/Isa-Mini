theory Iso_Base
  imports Minilang
begin

axiomatization PP :: "nat \<Rightarrow> bool" and QQ :: "nat \<Rightarrow> bool" where
  ax_ex: "\<exists>z. PP z" and
  ax_p3: "PP 3" and
  ax_q7: "QQ 7"

ML \<open>
fun report ctxt name =
  (case try (Proof_Context.get_thm ctxt) name of
     NONE => writeln ("##RESULT " ^ name ^ ": MISSING (proof failed)")
   | SOME th =>
      writeln ("##RESULT " ^ name ^ ": " ^
               Syntax.string_of_term ctxt (Thm.prop_of th) ^
               "  ||oracles=" ^ \<^make_string> (map #1 (Thm_Deps.all_oracles [th])) ^
               "  ||hyps=" ^ \<^make_string> (Thm.hyps_of th)))
\<close>

end
