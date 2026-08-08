theory Iso_OldConv
  imports Minilang
begin
axiomatization AA :: bool and PP :: "nat \<Rightarrow> bool"
ML \<open>
val ctxt = \<^context>
fun flat1 s = String.translate (fn #"\n" => " " | c => String.str c) s
fun str t = flat1 (Print_Mode.setmp [] (fn () => Syntax.string_of_term ctxt t) ())
fun probe label s =
  let val t = Syntax.read_prop ctxt s
      val ctxt' = Variable.declare_term t ctxt
      val ct = Thm.cterm_of ctxt' t
  in case Exn.capture (fn () => Minilang_Aux.iso_atomize ctxt' ct) () of
       Exn.Res th => writeln ("##OLD " ^ label ^ " IN= " ^ str t ^ " || OUT= " ^ str (Thm.term_of (Thm.rhs_of th)))
     | Exn.Exn e => (if Exn.is_interrupt e then Exn.reraise e else ();
                     writeln ("##OLD " ^ label ^ " IN= " ^ str t ^ " || EXN: " ^ flat1 (Runtime.exn_message e)))
  end
\<close>
ML \<open>
probe "O1 top-level unknown atom (OFCLASS)"      "OFCLASS(nat, order_class)";
probe "O2 unknown atom under ==>"                "AA \<Longrightarrow> OFCLASS(nat, order_class)";
probe "O3 unknown atom under !!"                 "\<And>x::nat. OFCLASS(nat, order_class)";
probe "O4 top-level &&& (today silently passed)" "PP 3 &&& PP 4";
probe "O5 &&& under ==>"                         "AA \<Longrightarrow> (PP 3 &&& PP 4)";
probe "O6 TERM at top level"                     "TERM (x::nat)";
probe "O7 TERM under ==>"                        "AA \<Longrightarrow> TERM (x::nat)";
\<close>
end
