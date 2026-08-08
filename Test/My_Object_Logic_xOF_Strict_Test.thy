theory My_Object_Logic_xOF_Strict_Test
  imports Minilang.Minilang
begin

(* MY_OBJECT_LOGIC_PLAN.md section 8-8, xOF site (aux.ML `atomize_back').
   At this site the input is a discharged, rulified rule; purely object-level
   rules always atomize completely, so the strict check can only fire when the
   rule's own statement carries a non-atomizable meta component.  The rule
   below has a prop-typed premise `PROP WWx' that survives discharge, so
   atomize_back's result keeps a meta `\<Longrightarrow>' -- {strict = true} must raise
   "Fail to atomize" as a readable command failure. *)

axiomatization AAx BBx :: bool and WWx :: "prop" where
  rmix: "PROP WWx \<Longrightarrow> AAx \<longrightarrow> BBx" and
  fAx: "AAx"

(* Positive control: the same discharge shape on a fully object-level rule
   goes through atomize_back and succeeds. *)
axiomatization CCx :: bool where
  robj: "AAx \<longrightarrow> CCx"

lemma "True"
  by (min_script \<open>SPECIALIZE res: robj WITH fAx  PRINT  END\<close>)

(* EXPECTED ERROR on the lemma below (this is the assertion, not a defect):
     exception CTERM raised (my_object_logic.ML): Fail to atomize ...
   presented as a min_script command failure; the theory continues. *)
lemma "True"
  by (min_script \<open>SPECIALIZE res: rmix WITH _ fAx  PRINT  END\<close>)

end
