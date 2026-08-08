theory Iso_Leak
  imports Minilang
begin

axiomatization AA :: bool and PP :: "nat \<Rightarrow> bool"

ML \<open>writeln "##L1 PRINT immediately after HAVE (preview items)"\<close>
lemma l1: "AA"
  apply (min_script \<open>HAVE h: "\<And>a::nat. (\<forall>x. PP x) \<Longrightarrow> PP a" PRINT SORRY SORRY\<close>)
  oops

ML \<open>writeln "##L2 PRINT after the HAVE block is CLOSED (real items)"\<close>
lemma l2: "AA"
  apply (min_script \<open>HAVE h: "\<And>a::nat. (\<forall>x. PP x) \<Longrightarrow> PP a" SORRY PRINT SORRY\<close>)
  oops

ML \<open>writeln "##L3 multi-shows HAVE (preruns uses Logic.dest_conjunctions)"\<close>
lemma l3: "AA"
  apply (min_script \<open>HAVE h1: "PP 3" and h2: "PP 4" PRINT SORRY_END_ALL SORRY\<close>)
  oops
ML \<open>writeln "##L-END"\<close>

end
