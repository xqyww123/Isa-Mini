theory Test_OFClass_RSN
  imports "Auto_Sledgehammer.Auto_Sledgehammer"
begin

(* Regression test for the raw `exception THM 1 raised ... RSN: no unifiers`
   leak from Obvious/HAMMER (see contrib/auto_sledgehammer sledgehammer_solver.ML).

   Cause: the improved-SH fastforce path classifies every candidate fact via
   `infer_type_of_rule` -> `chk_split` -> `Simpdata.mk_eq` -> `RS Eq_TrueI`.
   For type-class theorems (`*_class.super` / `*.intro_of_class`) whose
   conclusion is a raw Pure prop `OFCLASS(?'a, c_class)` (not `Trueprop _`),
   `RS Eq_TrueI` has no unifiers and raised a raw THM that escaped every
   Auto_Fail/ERROR guard and surfaced to the agent.

   Fix: detect & silently drop OFCLASS lemmas at the fact entry points, plus a
   defensive `handle THM _ => false` in `chk_split`.

   Run:
     cd contrib/Isa-Mini/Test
     ../../Isabelle2024/bin/isabelle process -l Auto_Sledgehammer -T Test_OFClass_RSN
   A failure raises an ML error (non-zero exit); success prints PASS lines. *)

ML \<open>
  val ctxt = @{context};

  (* (a) the general OFCLASS detector used by the fix (re-derived; the
     structure's copy is private). *)
  fun is_of_class_thm th =
    Term.exists_subterm (fn t => can Logic.dest_of_class t) (Thm.prop_of th);
  val _ =
    if is_of_class_thm @{thm Orderings.preorder_class.super}
       andalso not (is_of_class_thm @{thm disjE})
       andalso not (is_of_class_thm @{thm conjI})
    then writeln "PASS detector: OFCLASS lemma flagged, normal lemmas not"
    else error "FAIL detector: misclassification";

  (* (b) end-to-end: feeding an OFCLASS lemma to the solver on a goal it cannot
     prove must NOT raise a raw THM (pre-fix this raised THM 1: RSN: no
     unifiers). A clean failure (ERROR / Auto_Fail) or success is acceptable. *)
  val override =
    {add = [(Facts.named "Orderings.preorder_class.super", [])],
     del = [], only = false} : Sledgehammer_Fact.fact_override;
  val sequent = Goal.init (Thm.cterm_of ctxt @{prop "(P::nat \<Rightarrow> bool) n"});
  val _ =
    (Phi_Sledgehammer_Solver.auto true override NONE
        (SOME (Time.fromSeconds 8)) ctxt sequent;
     writeln "PASS end-to-end: solver returned without raising")
    handle THM (m,i,_) =>
             error ("FAIL end-to-end: raw THM " ^ string_of_int i ^ ": " ^ m)
         | ERROR _ => writeln "PASS end-to-end: clean ERROR, no raw THM";
  val _ = writeln "ALL PASS: Test_OFClass_RSN";
\<close>

end
