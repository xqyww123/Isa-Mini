theory Iso_NST
  imports Minilang
begin
ML \<open>
val ctxt = \<^context>
fun chk label s =
  let val t  = Syntax.read_prop ctxt s
      val st = Goal.init (Thm.cterm_of ctxt t)
   in writeln ("##NST " ^ label ^ " : goal = " ^
        Print_Mode.setmp [] (fn () => Syntax.string_of_term ctxt t) () ^
        "  -> need_standard_tac = " ^
        Bool.toString (Phi_Sledgehammer_Solver.need_standard_tac ctxt st))
  end
\<close>
ML \<open>
chk "bare OFCLASS"        "OFCLASS(nat, order_class)";
chk "plain HOL goal"      "(1::nat) = 1";
\<close>
end
