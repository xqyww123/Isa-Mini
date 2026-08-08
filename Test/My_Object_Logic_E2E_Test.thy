theory My_Object_Logic_E2E_Test
  imports Minilang.Minilang
begin

(* MY_OBJECT_LOGIC_PLAN.md section 8-1 end-to-end example.  Red baseline on the
   unswitched tree: PRINT showed  res : CC \<longrightarrow> All RR5 \<longrightarrow> BB  (binder name and
   eta-redex lost).  Expected after the aux.ML:292 switch:
   res : CC \<longrightarrow> (\<forall>yyy. RR5 yyy) \<longrightarrow> BB *)

axiomatization
      AA BB CC :: bool
  and RR5 :: "nat \<Rightarrow> bool"
where
      e2e_rule2 : "AA \<longrightarrow> (\<forall>yyy. RR5 yyy) \<longrightarrow> BB"
  and fA        : "CC \<Longrightarrow> AA"

lemma "True"
  by (min_script \<open>SPECIALIZE res: e2e_rule2 WITH fA  PRINT  END\<close>)

end
