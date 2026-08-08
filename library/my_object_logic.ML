(*  library/my_object_logic.ML

    The single facade over object-logic conversions: Minilang code calls
    My_Object_Logic, never Object_Logic directly.

    Object-logic layer: the system Object_Logic stays untouched; only the
    result of the thm-level `atomize' is repaired.  `Raw_Simplifier.rewrite_wrt'
    beta-eta-contracts it (binder names lost, e.g. `All RR5' for `\<forall>yyy. RR5 yyy'),
    while the term-level `atomize_term' is undamaged -- so the undamaged shape
    is recomputed from `atomize_term' and the damaged result is converted to it
    by a kernel beta-eta equation.  {strict = true} adds the completeness check
    from phi-system's iso_atomize.ML: a result that is not an object judgment
    raises "Fail to atomize"; {strict = false} is best-effort and never raises
    for incompleteness (printing paths).

    Iso layer: rule-driven reversible embedding of Pure connectives into
    object-level constants (`pure_*_embed', defined in Minilang.thy).  Engine
    Merely_Rewrite; rule sets are two iNet_Thm_Collection instances behind the
    attributes iso_atomize_rules / iso_rulify_rules (same names as phi-system's,
    so phi's declarations stay compatible).

    The layers share only the struct and `chk'.  Plan: MY_OBJECT_LOGIC_PLAN.md.
*)

signature MY_OBJECT_LOGIC =
sig
  val atomize_conv: {strict: bool} -> Proof.context -> conv
  val atomize: {strict: bool} -> Proof.context -> thm -> thm
  val atomize_term: {strict: bool} -> Proof.context -> term -> term
  val full_atomize_tac: {strict: bool} -> Proof.context -> int -> tactic
  val rulify: Proof.context -> thm -> thm    (*bare alias; no strict, no repair*)

  (*repair core, exported for acceptance injection (fake targets test the
    fallback branch): `eq' is the system equation (lhs = input), `term' the
    undamaged target*)
  val repair_or_fallback: Proof.context -> thm -> term -> thm

  (*precondition census: how often the system result was already intact, was
    repaired, or mismatched the target (fallback, expected never)*)
  val census: unit -> {intact: int, repaired: int, fallback: int}
  val reset_census: unit -> unit

  (*iso layer: reversible embedding, rule-driven, engine Merely_Rewrite*)
  val iso_atomize_conv: Proof.context -> conv
  val iso_rulify_conv: Proof.context -> conv
  val iso_atomize: Proof.context -> thm -> thm
  val iso_rulify: Proof.context -> thm -> thm
end

structure My_Object_Logic : MY_OBJECT_LOGIC =
struct

(** object-logic layer **)

val census_state =
  Synchronized.var "My_Object_Logic.census" {intact = 0, repaired = 0, fallback = 0};

fun census () = Synchronized.value census_state;
fun reset_census () =
  Synchronized.change census_state (K {intact = 0, repaired = 0, fallback = 0});

fun count_intact () = Synchronized.change census_state
      (fn {intact, repaired, fallback} =>
          {intact = intact + 1, repaired = repaired, fallback = fallback});
fun count_repaired () = Synchronized.change census_state
      (fn {intact, repaired, fallback} =>
          {intact = intact, repaired = repaired + 1, fallback = fallback});
fun count_fallback () = Synchronized.change census_state
      (fn {intact, repaired, fallback} =>
          {intact = intact, repaired = repaired, fallback = fallback + 1});

(*the undamaged target: `atomize_term' composes drop_judgment, so a bool result
  needs its Trueprop back*)
fun target_of ctxt t =
  let val t0 = Object_Logic.atomize_term ctxt t
  in if fastype_of t0 = \<^Type>\<open>bool\<close> then HOLogic.mk_Trueprop t0 else t0 end;

fun repair_or_fallback ctxt eq target =
  let val damaged = Thm.term_of (Thm.rhs_of eq) in
    if damaged aconv target then (count_intact (); eq)
    else if Envir.beta_eta_contract damaged aconv Envir.beta_eta_contract target
    then
      let
        val _ = count_repaired ();
        val eq_t = Drule.beta_eta_conversion (Thm.cterm_of ctxt target);  (*target \<equiv> nf*)
        val eq_d = Drule.beta_eta_conversion (Thm.rhs_of eq);             (*damaged \<equiv> nf*)
      in Thm.transitive eq (Thm.transitive eq_d (Thm.symmetric eq_t)) end
    else
     (count_fallback ();
      warning ("My_Object_Logic: atomize repair mismatch, returning the unrepaired result\n\
               \damaged: " ^ @{make_string} damaged ^ "\n\
               \target: " ^ @{make_string} target);
      eq)
  end;

(*completeness checks, phi semantics verbatim (phi iso_atomize.ML).  `chk' takes
  the equation theorem: its rhs must be Trueprop-headed; the exception payload
  is the equation's lhs (= the input -- repair keeps the lhs unchanged).*)
fun chk eq =
  (case Thm.prop_of eq
     of _ (*Pure.eq*) $ _ $ (Const (\<^const_name>\<open>Trueprop\<close>, _) $ _) => eq
      | _ => raise CTERM ("Fail to atomize", [Thm.dest_arg1 (Thm.cprop_of eq)]));

fun chk_term (Const (\<^const_name>\<open>Trueprop\<close>, _) $ X) = X
  | chk_term X =
      (case Term.fastype_of X
         of \<^Type>\<open>bool\<close> => X
          | _ => raise TERM ("Fail to atomize", [X]));

fun atomize_conv {strict} ctxt ct =
  (case Thm.term_of ct
     of Const (\<^const_name>\<open>Trueprop\<close>, _) $ _ => Conv.all_conv ct
      | _ =>
        let
          val eq = repair_or_fallback ctxt (Object_Logic.atomize ctxt ct)
                     (target_of ctxt (Thm.term_of ct));
        in if strict then chk eq else eq end);

fun atomize strict = Conv.fconv_rule o atomize_conv strict;

(*no repair at the term level -- the term-level engine is undamaged; strict only
  adds the completeness check, so {strict = false} is a verbatim alias*)
fun atomize_term {strict} ctxt t =
  let val t' = Object_Logic.atomize_term ctxt t
  in if strict then chk_term t' else t' end;

fun full_atomize_tac strict ctxt = CONVERSION (atomize_conv strict ctxt);

val rulify = Object_Logic.rulify;


(** iso layer **)

(*shared key function of both rule collections; self-raised so the user sees
  "iso_atomize_rules: rule is not a meta-equation", not a bare dest_equals*)
fun embed_rule_key th =
  #1 (Logic.dest_equals (Thm.prop_of th))
    handle TERM _ => raise THM ("rule is not a meta-equation", 0, [th]);

structure Atomize = iNet_Thm_Collection(
  val name = @{binding iso_atomize_rules}
  val description = "isomorphic atomize rules (meta-level connectives to object-level embeddings)"
  val key_of = embed_rule_key);

structure Rulify = iNet_Thm_Collection(
  val name = @{binding iso_rulify_rules}
  val description = "isomorphic rulify rules (object-level embeddings back to meta-level connectives)"
  val key_of = embed_rule_key);

val _ = Theory.setup (Atomize.setup #> Rulify.setup);

fun iso_atomize_conv ctxt ct =
  (case Thm.term_of ct
     of Const (\<^const_name>\<open>Trueprop\<close>, _) $ _ => Conv.all_conv ct
      | _ => chk (Merely_Rewrite.rewrite_conv (Atomize.get_net ctxt) ctxt ct));

fun iso_rulify_conv ctxt = Merely_Rewrite.rewrite_conv (Rulify.get_net ctxt) ctxt;

val iso_atomize = Conv.fconv_rule o iso_atomize_conv;
val iso_rulify = Conv.fconv_rule o iso_rulify_conv;

end
