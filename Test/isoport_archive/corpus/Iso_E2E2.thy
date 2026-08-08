theory Iso_E2E2
  imports Minilang
begin

axiomatization AA :: bool and PP :: "nat \<Rightarrow> bool"

ML \<open>writeln "##E4 HAVE with an eta-contractible HOL subterm in its statement"\<close>
lemma e4: "AA"
  apply (min_script \<open>HAVE "\<And>a::nat. (\<forall>x. PP x) \<Longrightarrow> PP a" PRINT SORRY SORRY\<close>)
  oops
ML \<open>writeln "##E4-END"\<close>

end
