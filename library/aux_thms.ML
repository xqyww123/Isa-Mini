signature MINILANG_AUX = sig

structure Thms : sig
  val TrueI : thm
  val allI : thm
  val spec : thm
  val impI : thm
  val exI : thm
  val ex1I : thm
  val exE : thm
  val conjI : thm
  val conjE : thm
  val disjE : thm
  val conjunctionD1 : thm
  val conjunctionD2 : thm
  val conjunct1 : thm
  val conjunct2 : thm
  val conj_imp_eq_imp_imp : thm
  val prop_def : thm
  val prop_def'sym : thm

  val atomize_all     : thm
  val atomize_all'sym : thm
  val atomize_imp     : thm
  val atomize_imp'sym : thm

  val GOAL_def : thm
  val GOAL_def'sym : thm
  val TAG_def : thm
  val TAG_def'sym : thm

  val conjunction_imp : thm
  val conjunction_imp'sym : thm

end

val iso_atomize : Proof.context -> conv
val iso_rulify  : Proof.context -> conv
val iso_atomize': Proof.context -> thm -> thm
val iso_rulify' : Proof.context -> thm -> thm
val concl_conv : (Proof.context -> conv) -> Proof.context -> conv

end

structure Minilang_Aux : MINILANG_AUX = struct

structure Thms = struct
val TrueI = @{thm TrueI}
val allI = @{thm allI}
val spec = @{thm spec}
val impI = @{thm impI}
val exI = @{thm exI}
val exE = @{thm exE}
val ex1I = @{thm ex1I}
val conjI= @{thm conjI}
val conjE = @{thm conjE}
val disjE = @{thm disjE}
val conjunctionD1 = @{thm Pure.conjunctionD1}
val conjunctionD2 = @{thm Pure.conjunctionD2}
val conjunct1 = @{thm HOL.conjunct1}
val conjunct2 = @{thm HOL.conjunct2}
val conj_imp_eq_imp_imp = @{lemma "(P \<and> Q \<Longrightarrow> PROP R) \<equiv> (P \<Longrightarrow> Q \<Longrightarrow> PROP R)"
                               by standard simp_all}
val prop_def = @{thm Pure.prop_def}
val prop_def'sym = @{thm Pure.prop_def[symmetric]}

val atomize_all = @{thm atomize_all}
val atomize_all'sym = @{thm atomize_all[symmetric]}
val atomize_imp = @{thm atomize_imp}
val atomize_imp'sym = @{thm atomize_imp[symmetric]}

val GOAL_def     = @{thm GOAL_def}
val GOAL_def'sym = @{thm GOAL_def[symmetric]}
val TAG_def      = @{thm TAG_def}
val TAG_def'sym  = @{thm TAG_def[symmetric]}

val ISO_ALL_def  = @{thm atomize_all[folded ISO_ALL_def, symmetric]}
val ISO_ALL'sym_def  = @{thm atomize_all[folded ISO_ALL_def]}
val ISO_IMP_def  = @{thm atomize_imp[folded ISO_IMP_def, symmetric]}
val ISO_IMP'sym_def  = @{thm atomize_imp[folded ISO_IMP_def]}
val ISO_PROP_def  = @{thm ISO_PROP}
val ISO_PROP'sym_def  = @{thm ISO_PROP[symmetric]}

val conjunction_imp = @{thm conjunction_imp}
val conjunction_imp'sym = @{thm conjunction_imp[symmetric]}

end

fun combination_conv' cv1 cv2 ct =
  let val (ct1, ct2) = Thm.dest_comb ct
      val y2 = (cv2 ct2)
      val y1 = (cv1 ct1)
  in Thm.combination y1 y2 end;

fun iso_atomize ctxt ctm =
  let open Conv
   in case Thm.term_of ctm
   of Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ =>
        ( combination_conv (arg_conv (iso_atomize ctxt))
                           (iso_atomize ctxt)
          then_conv rewr_conv Thms.ISO_IMP'sym_def
        ) ctm
    | Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs _ =>
        ( arg_conv (abs_conv (iso_atomize o snd) ctxt)
          then_conv rewr_conv Thms.ISO_ALL'sym_def
        ) ctm
    | Const(\<^const_name>\<open>Pure.prop\<close>, _) $ _ =>
        ( rewr_conv Thms.ISO_PROP'sym_def ) ctm
    | _ => all_conv ctm
  end

fun iso_rulify ctxt ctm =
  let open Conv
   in case Thm.term_of ctm
   of _ $ (Const(\<^const_name>\<open>ISO_IMP\<close>, _) $ _ $ _) =>
        ( rewr_conv Thms.ISO_IMP_def then_conv
          combination_conv (arg_conv (iso_rulify ctxt))
                           (iso_rulify ctxt) 
        ) ctm
    | _ $ (Const(\<^const_name>\<open>ISO_ALL\<close>, _) $ Abs _) =>
        ( rewr_conv Thms.ISO_ALL_def then_conv
          arg_conv (abs_conv (iso_rulify o snd) ctxt)
        ) ctm
    | _ $ (Const(\<^const_name>\<open>ISO_PROP\<close>, _) $ _) =>
        ( rewr_conv Thms.ISO_PROP_def ) ctm
    | _ => all_conv ctm
  end

val iso_atomize' = Conv.fconv_rule o iso_atomize
val iso_rulify'  = Conv.fconv_rule o iso_rulify

fun concl_conv C ctxt ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ =>
          ( Conv.arg_conv (concl_conv C ctxt) ) ctm
     | Const(\<^const_name>\<open>Pure.all\<close>, _) $ _ $ Abs _ =>
          ( Conv.arg_conv (Conv.abs_conv (concl_conv C o snd) ctxt) ) ctm
     | Const(\<^const_name>\<open>Pure.prop\<close>, _) $ _ =>
          ( Conv.arg_conv (C ctxt) ) ctm
     | Const(\<^const_name>\<open>GOAL\<close>, _) $ _ =>
          ( Conv.arg_conv (concl_conv C ctxt) ) ctm
     | _ => C ctxt ctm

end