theory My_Object_Logic_Transitions_Test
  imports Minilang.Minilang
begin

(* MY_OBJECT_LOGIC_PLAN.md section 8-4, whitelist item (b): positive controls
   for the error-to-success transitions the atomize repair enables.  Both
   lemmas were run against the pre-switch checkout (commit e44c188) on
   2026-08-08; the empirical outcome:

   - Lemma 1 (named instantiation) is a REGISTERED TRANSITION: on the old
     tree the first SPECIALIZE's atomize_back eta-contracted its result to
     `CC \<longrightarrow> All RR5`, so after discharging CC the by-name instantiation died
     with `cannot instantiate rule <resm>: Variable "yyy" is not found in the
     rule`.  On the repaired tree it succeeds (res2 : RR5 5).

   - Lemma 2 (chained xOF) is NOT a transition: it passes on BOTH trees.
     Discharge unification is modulo beta-eta, so even the damaged
     `CC \<longrightarrow> All RR5 \<longrightarrow> BB` premise discharges against fAll.  It stays here
     as the chained positive control over a damaged-on-the-old-tree
     intermediate. *)

axiomatization AA BB CC :: bool and RR5 :: "nat \<Rightarrow> bool" where
  tr_rule:  "AA \<longrightarrow> (\<forall>yyy. RR5 yyy)" and
  tr_rule2: "AA \<longrightarrow> (\<forall>yyy. RR5 yyy) \<longrightarrow> BB" and
  fA: "CC \<Longrightarrow> AA" and
  fAll: "\<forall>zzz. RR5 zzz" and
  fCC: "CC"

(* transition 1: named instantiation (where) of a repaired result.  The first
   SPECIALIZE's atomize_back fires on `CC \<Longrightarrow> Trueprop (\<forall>yyy. RR5 yyy)`; on the
   unswitched tree the whole result was beta-eta-contracted to `CC \<longrightarrow> All RR5`,
   so after discharging CC the binder name `yyy` no longer existed and the
   by-name instantiation failed. *)
lemma "True"
  by (min_script \<open>
    SPECIALIZE res: tr_rule WITH fA
    SPECIALIZE resm: res WITH fCC
    SPECIALIZE res2: resm where yyy = "5 :: nat"  PRINT
    END\<close>)

(* chained xOF through a damaged-on-the-old-tree intermediate: the repaired
   result is the rule of a second SPECIALIZE whose discharge meets the
   restored \<forall>-premise *)
lemma "True"
  by (min_script \<open>
    SPECIALIZE res: tr_rule2 WITH fA
    SPECIALIZE res2: res WITH fCC fAll  PRINT
    END\<close>)

end
