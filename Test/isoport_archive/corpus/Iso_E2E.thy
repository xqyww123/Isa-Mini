theory Iso_E2E
  imports Minilang
begin

axiomatization AA :: bool and BB :: bool
           and PP :: "nat \<Rightarrow> bool" and RR5 :: "nat \<Rightarrow> bool"

ML \<open>writeln "##E2E-1 eta case"\<close>
lemma e1: "\<And>a. \<lbrakk>AA \<and> BB; \<forall>x. PP x\<rbrakk> \<Longrightarrow> PP a \<and> AA"
  apply (min_script \<open>PRINT SORRY\<close>)
  oops

ML \<open>writeln "##E2E-2 binder name case"\<close>
lemma e2: "AA"
  apply (min_script \<open>HAVE "\<And>yyy::nat. RR5 yyy" PRINT SORRY SORRY\<close>)
  oops

ML \<open>writeln "##E2E-3 OFCLASS case"\<close>
lemma ofc: "OFCLASS(nat, order_class)"
  apply (min_script \<open>PRINT SORRY\<close>)
  oops
ML \<open>writeln "##E2E-END"\<close>

end
