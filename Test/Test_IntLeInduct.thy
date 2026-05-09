theory Test_IntLeInduct
  imports Minilang.Minilang
begin

ML \<open>
  val thm = @{thm int_le_induct}
  val _ = writeln ("thm: " ^ Thm.string_of_thm \<^context> thm)
  val _ = writeln ("nprems: " ^ string_of_int (Thm.nprems_of thm))
  val _ = writeln ("prop: " ^ ML_Syntax.print_term (Thm.prop_of thm))
\<close>

end
