(* The base of Phi_Conv, a general conversion toolbox.  It is seeded HERE, at
   the lowest Minilang layer, rather than in phi-system, because its consumers
   sit below phi: phi-system's Phi_Logic_Programming_Reasoner already imports
   Minilang_AoA, so its library files extend this structure by the usual
   `include PHI_CONV` / `open Phi_Conv` pattern. *)
signature PHI_CONV = sig

(* alpha_beta_eta_conv target ct : ct ≡ target, whenever the two differ only
   by alpha/beta/eta (alpha is free — Thm.transitive's middle-term test is
   aconv).  Apply with Conv.fconv_rule: when nothing changed the equation is
   reflexive and the same thm object comes back.  A difference beyond
   alpha/beta/eta makes Thm.transitive raise THM; it can never yield a wrong
   equation, because the kernel checks both halves. *)
val alpha_beta_eta_conv : cterm -> conv

(* alpha_beta_eta_inst_conv orig ct : the same, but the target is `orig` under
   the instantiation this proof actually made — ct ≡ orig σ, where σ matches
   orig against ct.  Undoing an instantiation would be unsound (a proof of
   `P t` is not a proof of `P ?v`), so legitimate instantiations are KEPT and
   only the incidental alpha/beta/eta churn and Var re-indexing are undone.
   Matching runs on the beta-eta normal forms (Pattern.match refuses a pattern
   whose head is an Abs, which a conclusion carrying a beta-redex would have),
   while the target is built from the UN-normalised orig so its verbatim shape
   comes back.  Soundness never depends on the match: a bogus σ merely makes
   Thm.transitive raise. *)
val alpha_beta_eta_inst_conv : cterm -> conv

end

structure Phi_Conv : PHI_CONV = struct

fun alpha_beta_eta_conv target ct =
  Thm.transitive (Drule.beta_eta_conversion ct)
                 (Thm.symmetric (Drule.beta_eta_conversion target))

fun alpha_beta_eta_inst_conv orig ct =
  let val nf = Thm.rhs_of o Drule.beta_eta_conversion
      val target =
        (* Only Pattern.MATCH means "not an instance"; it already falls back to
           first-order matching internally (Pure/pattern.ML), so no second
           attempt is needed here. *)
        (Thm.instantiate_cterm (Thm.match (nf orig, nf ct)) orig
         handle Pattern.MATCH => orig)
   in alpha_beta_eta_conv target ct
  end

end

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

val concl_conv : (Proof.context -> conv) -> Proof.context -> conv

val simp_fact_name' : string -> string

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

val conjunction_imp = @{thm conjunction_imp}
val conjunction_imp'sym = @{thm conjunction_imp[symmetric]}

end

fun combination_conv' cv1 cv2 ct =
  let val (ct1, ct2) = Thm.dest_comb ct
      val y2 = (cv2 ct2)
      val y1 = (cv1 ct1)
  in Thm.combination y1 y2 end;

fun concl_conv C ctxt ctm =
  case Thm.term_of ctm
    of Const(\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ =>
          ( Conv.arg_conv (concl_conv C ctxt) ) ctm
       (* Pure.all is UNARY: the old binary pattern `$ _ $ Abs _` could never
          match, so a ⋀-topped term always fell to the catch-all and had C
          applied to the WHOLE term (stage 4f, §2.5). *)
     | Const(\<^const_name>\<open>Pure.all\<close>, _) $ Abs _ =>
          ( Conv.arg_conv (Conv.abs_conv (concl_conv C o snd) ctxt) ) ctm
     | Const(\<^const_name>\<open>Pure.prop\<close>, _) $ _ =>
          ( Conv.arg_conv (C ctxt) ) ctm
     | Const(\<^const_name>\<open>GOAL\<close>, _) $ _ =>
          ( Conv.arg_conv (concl_conv C ctxt) ) ctm
     | _ => C ctxt ctm

(* Lives here (not aux.ML) so that unify_diagnostic.ML can load before
   aux.ML: aux.ML's xOF needs Unify_Diagnostic for its failure messages. *)
fun simp_fact_name' name =
  if String.isPrefix "local." name
  then String.substring (name, 6, size name - 6)
  else name

end