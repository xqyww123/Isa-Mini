signature MINILANG_HELPER = sig

val guess_default_num_typ : term -> typ option
val implode_with : 'a -> 'a list list -> 'a list
val xsymmetric : Proof.context -> thm -> thm

end

structure Minilang_Helper : MINILANG_HELPER = struct

val realT = Type("Real.real", [])
fun guess_default_num_typ prop =
  if exists_type (exists_subtype (fn Type ("Real.real", _) => true | _ => false)) prop
  then SOME realT
  else if exists_type (exists_subtype (fn Type ("Int.int", _) => true | _ => false)) prop
  then SOME \<^typ>\<open>int\<close>
  else if exists_type (exists_subtype (fn Type (\<^type_name>\<open>nat\<close>, _) => true | _ => false)) prop
  then SOME \<^typ>\<open>nat\<close>
  else SOME \<^typ>\<open>int\<close>

fun implode_with sep [] = []
  | implode_with sep [x] = x
  | implode_with sep (xs :: lss) = xs @ sep :: implode_with sep lss

local
  val xsym_rewrites = [
    @{lemma \<open>(s = t) \<equiv> (t = s)\<close> by (simp add: atomize_eq eq_commute)},
    @{lemma \<open>(t \<noteq> s) \<equiv> (s \<noteq> t)\<close> by (simp add: atomize_eq eq_commute)},
    @{lemma \<open>((a, b) \<in> r) \<equiv> ((b, a) \<in> r\<inverse>)\<close> by (auto simp: atomize_eq)},
    @{lemma \<open>((a, b) \<in> r\<inverse>) \<equiv> ((b, a) \<in> r)\<close> by (auto simp: atomize_eq)},
    @{lemma \<open>equivclp r x y \<equiv> equivclp r y x\<close> by (simp add: atomize_eq, meson equivclp_sym)},
    @{lemma \<open>(symclp r)\<^sup>*\<^sup>* x y \<equiv> (symclp r)\<^sup>*\<^sup>* y x\<close>
        by (simp add: atomize_eq, meson rtranclp_symclp_sym)},
    @{lemma \<open>(x \<equiv> y) \<equiv> (y \<equiv> x)\<close> by (simp add: atomize_eq eq_commute)}
  ]

  fun xsym_conv ctxt ct =
    (case Thm.term_of ct of
      Const ("Pure.all", _) $ Abs _ =>
        Conv.arg_conv (Conv.abs_conv (fn (_, c) => xsym_conv c) ctxt) ct
    | Const ("Pure.imp", _) $ _ $ _ =>
        Conv.arg_conv (xsym_conv ctxt) ct
    | Const (\<^const_name>\<open>Trueprop\<close>, _) $ _ =>
        Conv.arg_conv (xsym_conv ctxt) ct
    | Const (\<^const_name>\<open>All\<close>, _) $ Abs _ =>
        Conv.arg_conv (Conv.abs_conv (fn (_, c) => xsym_conv c) ctxt) ct
    | Const (\<^const_name>\<open>implies\<close>, _) $ _ $ _ =>
        Conv.arg_conv (xsym_conv ctxt) ct
    | Const (\<^const_name>\<open>conj\<close>, _) $ _ $ _ =>
        Conv.combination_conv (Conv.arg_conv (xsym_conv ctxt)) (xsym_conv ctxt) ct
    | Const (\<^const_name>\<open>disj\<close>, _) $ _ $ _ =>
        Conv.combination_conv (Conv.arg_conv (xsym_conv ctxt)) (xsym_conv ctxt) ct
    | _ => Conv.first_conv (map Conv.rewr_conv xsym_rewrites) ct)
in

fun xsymmetric ctxt th =
  (case Calculation.symmetric (Context.Proof ctxt, th) of
    (_, SOME th') => th'
  | _ => Conv.fconv_rule (xsym_conv ctxt) th)
  handle THM _ => Conv.fconv_rule (xsym_conv ctxt) th

end

end
