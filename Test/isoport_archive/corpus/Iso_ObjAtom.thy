theory Iso_ObjAtom
  imports Minilang
begin

axiomatization AA :: bool and BB :: bool
           and PP :: "nat \<Rightarrow> bool" and RR5 :: "nat \<Rightarrow> bool"

ML \<open>
val ctxt = \<^context>
fun flat1 s = String.translate (fn #"\n" => " " | c => String.str c) s
fun str t = flat1 (Print_Mode.setmp [] (fn () => Syntax.string_of_term ctxt t) ())
fun show label s =
  let val t   = Syntax.read_prop ctxt s
      val ctxt' = Variable.declare_term t ctxt
      val raw = case try (fn () => Thm.term_of (Thm.rhs_of (Object_Logic.atomize ctxt' (Thm.cterm_of ctxt' t)))) () of
                   SOME r => r | NONE => t
      val a   = Object_Logic.atomize_term ctxt' t
      val had_trueprop = case raw of Const(\<^const_name>\<open>Trueprop\<close>,_) $ _ => true | _ => false
      val still_trueprop = case a of Const(\<^const_name>\<open>Trueprop\<close>,_) $ _ => true | _ => false
   in writeln ("##OA " ^ label ^
               "\n     IN : " ^ str t ^
               "\n     OUT: " ^ str a ^
               "\n     raw_rewrite_had_Trueprop_head=" ^ Bool.toString had_trueprop ^
               "  after_drop_judgment_still_Trueprop=" ^ Bool.toString still_trueprop)
  end
\<close>

ML \<open>
show "T1 binder-name, eta-contractible body" "\<And>yyy::nat. RR5 yyy";
show "T2 binder-name under imp"              "\<And>yyy::nat. RR5 yyy \<Longrightarrow> AA";
show "T3 HOL All in premise"                 "(\<forall>x. PP x) \<Longrightarrow> AA";
show "T4 MS_Test shape"                      "\<And>a. \<lbrakk>AA \<and> BB; \<forall>x. PP x\<rbrakk> \<Longrightarrow> PP a \<and> AA";
show "T5 two binders"                        "\<And>yyy zzz::nat. RR5 yyy \<and> RR5 zzz";
show "T6 HOL All in conclusion"              "AA \<Longrightarrow> (\<forall>x. PP x)";
show "T7 nested meta-all under imp"          "\<And>zzz::nat. RR5 zzz \<Longrightarrow> (\<And>www::nat. PP www)";
writeln ("##OA min_shell_atomize_goals default = " ^
         Bool.toString (Config.get \<^context> Minilang.atomize_goals_in_printing));
\<close>

end
