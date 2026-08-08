theory Iso_Ctx
  imports Minilang
begin
axiomatization AA :: bool and RR5 :: "nat \<Rightarrow> bool"
ML \<open>writeln "##CTX-2 shared-tree baseline: two adjacent meta-binders in the conclusion"\<close>
lemma ctx2: "\<And>yyy zzz::nat. RR5 yyy \<and> RR5 zzz"
  apply (min_script \<open>PRINT SORRY\<close>)
  oops
ML \<open>writeln "##CTX-3 shared-tree baseline: HAVE with two adjacent meta-binders"\<close>
lemma ctx3: "AA"
  apply (min_script \<open>HAVE h: "\<And>yyy zzz::nat. RR5 yyy \<and> RR5 zzz" PRINT SORRY SORRY\<close>)
  oops
ML \<open>writeln "##CTX-END"\<close>
end
