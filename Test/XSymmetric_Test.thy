theory XSymmetric_Test
  imports Complex_Main
begin

ML \<open>
(* Pre-prove the 7 sym rules as meta-equalities for Conv.rewr_conv *)
local
  fun mk_meta_eq th = th RS @{thm eq_reflection}
in
  (* Self-symmetric rules *)
  val eq_sym_eq = mk_meta_eq @{lemma \<open>(s = t) = (t = s)\<close> by auto}
  val neq_sym_eq = mk_meta_eq @{lemma \<open>(t \<noteq> s) = (s \<noteq> t)\<close> by auto}
  val equivclp_sym_eq = mk_meta_eq
    @{lemma \<open>equivclp r x y = equivclp r y x\<close> by (meson equivclp_sym)}
  val symclp_rtranclp_sym_eq = mk_meta_eq
    @{lemma \<open>(symclp r)\<^sup>*\<^sup>* x y = (symclp r)\<^sup>*\<^sup>* y x\<close> by (meson rtranclp_symclp_sym)}
  (* Converse pair *)
  val converse_mem_sym_eq = mk_meta_eq
    @{lemma \<open>((a, b) \<in> r) = ((b, a) \<in> r\<inverse>)\<close> by auto}
  val converse_mem_sym_eq2 = mk_meta_eq
    @{lemma \<open>((a, b) \<in> r\<inverse>) = ((b, a) \<in> r)\<close> by auto}
  (* Pure.eq: construct (x \<equiv> y) \<equiv> (y \<equiv> x) *)
  val pure_eq_sym_eq =
    let val x = Free ("x", TFree ("'a", \<^sort>\<open>type\<close>))
        val y = Free ("y", TFree ("'a", \<^sort>\<open>type\<close>))
        val ctxt = \<^context>
        val xy = Thm.assume (Thm.cterm_of ctxt (Logic.mk_equals (x, y)))
        val yx = Thm.assume (Thm.cterm_of ctxt (Logic.mk_equals (y, x)))
        val fwd = Thm.implies_intr (Thm.cprop_of xy) (Thm.symmetric xy)
        val bwd = Thm.implies_intr (Thm.cprop_of yx) (Thm.symmetric yx)
    in Thm.generalize (Names.make_set ["'a"], Names.make_set ["x", "y"]) 0
         (Thm.equal_intr fwd bwd) end
end;

val _ = writeln ("eq_sym_eq: " ^ Syntax.string_of_term \<^context> (Thm.prop_of eq_sym_eq))
val _ = writeln ("neq_sym_eq: " ^ Syntax.string_of_term \<^context> (Thm.prop_of neq_sym_eq))
val _ = writeln ("equivclp_sym_eq: " ^ Syntax.string_of_term \<^context> (Thm.prop_of equivclp_sym_eq))
val _ = writeln ("symclp_rtranclp_sym_eq: " ^ Syntax.string_of_term \<^context> (Thm.prop_of symclp_rtranclp_sym_eq))
val _ = writeln ("converse_mem_sym_eq: " ^ Syntax.string_of_term \<^context> (Thm.prop_of converse_mem_sym_eq))
val _ = writeln ("converse_mem_sym_eq2: " ^ Syntax.string_of_term \<^context> (Thm.prop_of converse_mem_sym_eq2))
val _ = writeln ("pure_eq_sym_eq: " ^ Syntax.string_of_term \<^context> (Thm.prop_of pure_eq_sym_eq))
\<close>

text \<open>Now test xsymmetric\<close>
ML \<open>
local
  val hol_sym_rewrites = [eq_sym_eq, neq_sym_eq, converse_mem_sym_eq, converse_mem_sym_eq2,
                          equivclp_sym_eq, symclp_rtranclp_sym_eq]

  fun xsym_conv ctxt ct =
    (case Thm.term_of ct of
      Const ("Pure.all", _) $ Abs _ =>
        Conv.arg_conv (Conv.abs_conv (fn (_, ctxt') => xsym_conv ctxt') ctxt) ct
    | Const ("Pure.imp", _) $ _ $ _ =>
        Conv.arg_conv (xsym_conv ctxt) ct
    | Const ("Pure.eq", _) $ _ $ _ =>
        Conv.rewr_conv pure_eq_sym_eq ct
    | \<^Const_>\<open>Trueprop for _\<close> =>
        Conv.arg_conv (xsym_conv ctxt) ct
    | \<^Const_>\<open>All _ for \<open>Abs _\<close>\<close> =>
        Conv.arg_conv (Conv.abs_conv (fn (_, ctxt') => xsym_conv ctxt') ctxt) ct
    | \<^Const_>\<open>implies for _ _\<close> =>
        Conv.arg_conv (xsym_conv ctxt) ct
    | \<^Const_>\<open>conj for _ _\<close> =>
        Conv.combination_conv (Conv.arg_conv (xsym_conv ctxt)) (xsym_conv ctxt) ct
    | \<^Const_>\<open>disj for _ _\<close> =>
        Conv.combination_conv (Conv.arg_conv (xsym_conv ctxt)) (xsym_conv ctxt) ct
    | _ => Conv.first_conv (map Conv.rewr_conv hol_sym_rewrites) ct)
in

fun xsymmetric ctxt th =
  \<^try>\<open>
    (case Calculation.symmetric (Context.Proof ctxt, th) of
      (_, SOME th') => th'
    | _ => raise THM ("symmetric", 0, [th]))
  catch _ => Conv.fconv_rule (xsym_conv ctxt) th
  \<close>

end;

(* === Tests === *)
local
  val ctxt = \<^context>
  fun test name thm =
    let
      val _ = writeln ("\n--- " ^ name ^ " ---")
      val _ = writeln ("  input:  " ^ Syntax.string_of_term ctxt (Thm.prop_of thm))
      val result = \<^try>\<open>
        let val thm' = xsymmetric ctxt thm
        in writeln ("  output: " ^ Syntax.string_of_term ctxt (Thm.prop_of thm'));
           "OK" end
        catch exn => "FAILED: " ^ Runtime.exn_message exn
      \<close>
    in writeln ("  => " ^ result) end
in val _ = (
  let
    val ([th0], _) = Assumption.add_assumes
      [\<^cprop>\<open>(a::nat) = b\<close>] ctxt
    val _ = test "bare eq (assumed)" th0

    val ([th1], ctxt1) = Assumption.add_assumes
      [\<^cprop>\<open>\<forall>z::nat. f z = z + 1\<close>] ctxt
    val _ = test "forall eq (assumed)" th1

    val ([th2], _) = Assumption.add_assumes
      [\<^cprop>\<open>\<forall>x::int. \<forall>y::int. x + y = y + x\<close>] ctxt
    val _ = test "nested forall eq (assumed)" th2

    val ([th3], _) = Assumption.add_assumes
      [\<^cprop>\<open>P \<longrightarrow> (a::nat) = b\<close>] ctxt
    val _ = test "implies eq (assumed)" th3

    val ([th4], _) = Assumption.add_assumes
      [\<^cprop>\<open>\<forall>x::nat. P x \<longrightarrow> f x = g x\<close>] ctxt
    val _ = test "forall implies eq (assumed)" th4

    val ([th5], _) = Assumption.add_assumes
      [\<^cprop>\<open>(a::nat) = b \<and> (c::nat) = d\<close>] ctxt
    val _ = test "conj eq (assumed)" th5

    val ([th6], _) = Assumption.add_assumes
      [\<^cprop>\<open>(a::nat) \<noteq> b\<close>] ctxt
    val _ = test "bare neq (assumed)" th6

    val ([th7], _) = Assumption.add_assumes
      [\<^cprop>\<open>\<forall>x::nat. f x \<noteq> g x\<close>] ctxt
    val _ = test "forall neq (assumed)" th7
  in () end
  )
end
\<close>

end
