theory Iso_GoalSide
  imports Minilang
begin

axiomatization AA :: bool and QQ :: "nat \<Rightarrow> bool" and PP :: "nat \<Rightarrow> bool"

ML \<open>writeln "##G1 schematic_goal, PRINT at top level (concl is iso-atomized)"\<close>
schematic_goal g1: "QQ (?x::nat)"
  apply (min_script \<open>PRINT SORRY\<close>)
  oops

ML \<open>writeln "##G2 multi-shows lemma, PRINT at top level (concl is A &&& B)"\<close>
lemma g2: shows ga: "PP 3" and gb: "QQ 7"
  apply (min_script \<open>PRINT SORRY SORRY\<close>)
  oops

ML \<open>writeln "##G3 meta-level goal shape at top level"\<close>
lemma g3: "\<And>yyy::nat. (\<forall>x. PP x) \<Longrightarrow> PP yyy"
  apply (min_script \<open>PRINT SORRY\<close>)
  oops
ML \<open>writeln "##G-END"\<close>

end
